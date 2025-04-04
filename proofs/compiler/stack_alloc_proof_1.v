(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype fintype.
From mathcomp Require Import div ssralg.
From mathcomp Require Import word_ssrZ.
Require Import seq_extra psem psem_facts compiler_util low_memory.
Require Export stack_alloc.
Require slh_lowering_proof.
Import Utf8 Lia.

Local Open Scope seq_scope.
Local Open Scope Z_scope.

(* --------------------------------------------------------------------------- *)

(* Size of a value. *)
Notation size_val v := (size_of (type_of_val v)).

Lemma size_of_gt0 ty : 0 < size_of ty.
Proof. by case: ty. Qed.

Lemma size_slot_gt0 s : 0 < size_slot s.
Proof. by apply size_of_gt0. Qed.

Lemma size_of_le ty ty' : subtype ty ty' -> size_of ty <= size_of ty'.
Proof.
  case: ty => [||p|ws]; case:ty' => [||p'|ws'] //.
  + by move=> /eqP ->; lia.
  move=> /wsize_size_le.
  by apply Z.divide_pos_le.
Qed.

(* TODO : move elsewhere *)
(* but not clear where
   Uptr is defined in memory_model, no stype there
   stype is defined in type, no Uptr there
*)
Notation spointer := (sword Uptr) (only parsing).

Section WITH_PARAMS.

Context
  {wsw : WithSubWord}
  {dc:DirectCall}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  (pmap : pos_map)
  (glob_size : Z)
  (rsp rip : pointer).

Context
  (Slots : Sv.t)
  (Addr : slot -> pointer)
  (Writable : slot -> bool)
  (Align : slot -> wsize).

(* Any pointer in a slot is valid. *)
Definition slot_valid m := forall s p, Sv.In s Slots ->
  between (Addr s) (size_slot s) p U8 -> validw m Aligned p U8.

(* NOTE: disjoint_zrange already contains no_overflow conditions *)
(* Slots are disjoint from the source memory [ms]. *)
Definition disjoint_source ms :=
  forall s p, Sv.In s Slots -> validw ms Aligned p U8 ->
  disjoint_zrange (Addr s) (size_slot s) p (wsize_size U8).

(* Addresses of slots can be manipulated without risking overflows. *)
Hypothesis addr_no_overflow : forall s, Sv.In s Slots ->
  no_overflow (Addr s) (size_slot s).

(* Two distinct slots, with at least one of them writable, are disjoint. *)
Hypothesis disjoint_writable : forall s1 s2,
  Sv.In s1 Slots -> Sv.In s2 Slots -> s1 <> s2 ->
  Writable s1 ->
  disjoint_zrange (Addr s1) (size_slot s1) (Addr s2) (size_slot s2).

(* The address [Addr s] of a slot [s] is aligned w.r.t. [Align s]. *)
Hypothesis slot_align :
  forall s, Sv.In s Slots -> is_align (Addr s) (Align s).

(* Writable slots are disjoint from globals. *)
Hypothesis writable_not_glob : forall s, Sv.In s Slots -> Writable s ->
  0 < glob_size -> disjoint_zrange rip glob_size (Addr s) (size_slot s).

(* All pointers valid in memory [m0] are valid in memory [m].
   It is supposed to be applied with [m0] the initial target memory
   and [m] the current target memory.
*)
Definition valid_incl m0 m :=
  forall p, validw m0 Aligned p U8 -> validw m Aligned p U8.

(* ms: current source memory
   m0: initial target memory (just before the call to the current function)
   m : current target memory

   ms:
                                                    --------------------
                                                    |    mem source    |
                                                    --------------------

   m0:
                       --------------- ------------ --------------------
                       | other stack | |   glob   | |    mem source    |
                       --------------- ------------ --------------------

                                  ||
                                  || function call
                                  \/

   m:
   ------------------- --------------- ------------ --------------------
   |   stack frame   | | other stack | |   glob   | |    mem source    |
   ------------------- --------------- ------------ --------------------

*)

(* The memory zones that are not in a writable slot remain unchanged. *)
Definition mem_unchanged ms m0 m :=
  forall p, validw m0 Aligned p U8 -> ~ validw ms Aligned p U8 ->
  (forall s, Sv.In s Slots -> Writable s -> disjoint_zrange (Addr s) (size_slot s) p (wsize_size U8)) ->
  read m0 Aligned p U8 = read m Aligned p U8.

Record wf_global g ofs ws := {
  wfg_slot : Sv.In g Slots;
  wfg_writable : ~ Writable g;
  wfg_align : Align g = ws;
  wfg_offset : Addr g = (rip + wrepr Uptr ofs)%R
}.

Definition wbase_ptr sc :=
  if sc == Sglob then rip else rsp.

Record wf_direct (x : var) (s : slot) ofs ws cs sc := {
  wfd_slot : Sv.In s Slots;
  wfd_size : size_slot x <= cs.(cs_len);
  wfd_zone : 0 <= cs.(cs_ofs) /\ cs.(cs_ofs) + cs.(cs_len) <= size_slot s;
  wfd_writable : Writable s = (sc != Sglob);
  wfd_align : Align s = ws;
  wfd_offset : Addr s = (wbase_ptr sc + wrepr Uptr ofs)%R
}.

Record wf_regptr x xr := {
  wfr_type : is_sarr (vtype x);
  wfr_rtype : vtype xr = spointer;
  wfr_not_vrip : xr <> pmap.(vrip);
  wfr_not_vrsp : xr <> pmap.(vrsp);
  wfr_new : Sv.In xr pmap.(vnew);
  wfr_distinct : forall y yr,
    get_local pmap y = Some (Pregptr yr) -> x <> y -> xr <> yr
}.

Record wf_stkptr (x : var) (s : slot) ofs ws cs (xf : var) := {
  wfs_slot : Sv.In s Slots;
  wfs_type : is_sarr (vtype x);
  wfs_size : wsize_size Uptr <= cs.(cs_len);
  wfs_zone : 0 <= cs.(cs_ofs) /\ cs.(cs_ofs) + cs.(cs_len) <= size_slot s;
  wfs_writable : Writable s;
  wfs_align : Align s = ws;
  wfs_align_ptr : (Uptr <= ws)%CMP;
  wfs_offset_align : is_align (wrepr _ cs.(cs_ofs))%R Uptr;
  wfs_offset : Addr s = (rsp + wrepr Uptr ofs)%R;
  wfs_new : Sv.In xf pmap.(vnew);
  wfs_distinct : forall y s' ofs' ws' z' yf,
    get_local pmap y = Some (Pstkptr s' ofs' ws' z' yf) -> x <> y -> xf <> yf
}.

Definition wf_local x pk :=
  match pk with
  | Pdirect s ofs ws z sc => wf_direct x s ofs ws z sc
  | Pregptr xr => wf_regptr x xr
  | Pstkptr s ofs ws z xf => wf_stkptr x s ofs ws z xf
  end.

Class wf_pmap := {
  wt_len      : vtype pmap.(vxlen) = spointer;
  len_in_new  : Sv.In pmap.(vxlen) pmap.(vnew);
  len_neq_rip : pmap.(vxlen) <> pmap.(vrip);
  len_neq_rsp : pmap.(vxlen) <> pmap.(vrsp);
  len_neq_ptr : forall x p, Mvar.get pmap.(locals) x = Some (Pregptr p) -> pmap.(vxlen) <> p;
  wt_rip     : vtype pmap.(vrip) = spointer;
  wt_rsp     : vtype pmap.(vrsp) = spointer;
  rip_in_new : Sv.In pmap.(vrip) pmap.(vnew);
  rsp_in_new : Sv.In pmap.(vrsp) pmap.(vnew);
  wf_globals : forall g ofs ws, Mvar.get pmap.(globals) g = Some (ofs, ws) -> wf_global g ofs ws;
  wf_locals  : forall x pk, Mvar.get pmap.(locals) x = Some pk -> wf_local x pk;
  wf_vnew    : forall x pk, Mvar.get pmap.(locals) x = Some pk -> ~ Sv.In x pmap.(vnew)
}.

(* Registers (not introduced by the compiler) hold the same value in [vm1] and [vm2] *)
Definition eq_vm (vm1 vm2:Vm.t) :=
  forall (x:var),
    Mvar.get pmap.(locals) x = None ->
    ~ Sv.In x pmap.(vnew) ->
    vm1.[x] = vm2.[x].

(* Well-formedness of a [table] *)
Definition wft_VARS table :=
  forall x e,
    Mvar.get table.(bindings) x = Some e ->
    Sv.Subset (read_e e) table.(vars).

Definition wft_DEF vars vme :=
  forall x,
    Sv.In x vars ->
    exists2 v, get_var true vme x = ok v & type_of_val v = x.(vtype).

Fixpoint sem_sexpr vme (e : sexpr) :=
  match e with
  | Sconst z => ok (Vint z)
  | Svar v => get_var true vme v
  | Sof_int ws e =>
    Let v := sem_sexpr vme e in
    sem_sop1 (Oword_of_int ws) v
  | Sto_int ws e =>
    Let v := sem_sexpr vme e in
    sem_sop1 (Oint_of_word ws) v
  | Sneg opk e =>
    Let v := sem_sexpr vme e in
    sem_sop1 (Oneg opk) v
  | Sadd opk e1 e2 =>
    Let v1 := sem_sexpr vme e1 in
    Let v2 := sem_sexpr vme e2 in
    sem_sop2 (Oadd opk) v1 v2
  | Smul opk e1 e2 =>
    Let v1 := sem_sexpr vme e1 in
    Let v2 := sem_sexpr vme e2 in
    sem_sop2 (Omul opk) v1 v2
  | Ssub opk e1 e2 =>
    Let v1 := sem_sexpr vme e1 in
    Let v2 := sem_sexpr vme e2 in
    sem_sop2 (Osub opk) v1 v2
  end.

(* TODO: rewrite value_uincl vm1.[x] v2 ? *)
Definition wft_SEM table vme vm1 :=
  forall x e v1,
    Mvar.get table.(bindings) x = Some e ->
    get_var true vm1 x = ok v1 ->
    exists2 v2,
      sem_sexpr vme e = ok v2 &
      value_uincl v1 v2.

Record wf_table table vme vm1 := {
  wft_vars : wft_VARS table;
  wft_def : wft_DEF table.(vars) vme;
  wft_sem : wft_SEM table vme vm1;
}.

(* Well-formedness of a [region]. *)
Record wf_region (r : region) := {
  wfr_slot     : Sv.In r.(r_slot) Slots;
  wfr_writable : Writable r.(r_slot) = r.(r_writable);
  wfr_align    : Align r.(r_slot) = r.(r_align);
}.

(* We interpret a symbolic_slice as a concrete_slice *)
(* [vme] is for symbolic vmap *)
Definition sem_slice vme (s : symbolic_slice) : result error concrete_slice :=
  Let ofs := sem_sexpr vme s.(ss_ofs) >>= to_int in
  Let len := sem_sexpr vme s.(ss_len) >>= to_int in
  ok {| cs_ofs := ofs; cs_len := len |}.

Definition sub_concrete_slice cs1 cs2 :=
  if (0 <=? cs2.(cs_ofs)) && (cs2.(cs_ofs) + cs2.(cs_len) <=? cs1.(cs_len)) then
    ok {| cs_ofs := cs1.(cs_ofs) + cs2.(cs_ofs); cs_len := cs2.(cs_len) |}
  else Error ErrOob.

(* We interpret a symbolic_zone also as a concrete_slice *)
Fixpoint sem_zone_aux vme cs z :=
  match z with
  | [::] => ok cs
  | s1 :: z =>
    Let cs1 := sem_slice vme s1 in
    Let cs2 := sub_concrete_slice cs cs1 in
    sem_zone_aux vme cs2 z
  end.

Definition sem_zone vme z :=
  match z with
  | [::] => type_error
  | s :: z =>
    Let cs := sem_slice vme s in
    sem_zone_aux vme cs z
  end.

(* Well-formedness of a [concrete_slice]. *)
Record wf_concrete_slice (cs : concrete_slice) (ty : stype) (sl : slot) := {
  wfcs_len : size_of ty <= cs.(cs_len);
    (* the zone is big enough to store a value of type [ty] *)
  wfcs_ofs : 0 <= cs.(cs_ofs) /\ cs.(cs_ofs) + cs.(cs_len) <= size_slot sl
    (* the zone is a small enough to be in slot [sl] *)
}.

Definition wf_zone vme z ty sl :=
  exists2 cs,
    sem_zone vme z = ok cs &
    wf_concrete_slice cs ty sl.

(* Well-formedness of a [sub_region]. *)
Record wf_sub_region vme (sr : sub_region) ty := {
  wfsr_region :> wf_region sr.(sr_region);
  wfsr_zone   :> wf_zone vme sr.(sr_zone) ty sr.(sr_region).(r_slot)
}.

Definition wfr_WF (rmap : region_map) vme :=
  forall x sr,
    Mvar.get rmap.(var_region) x = Some sr ->
    wf_sub_region vme sr x.(vtype).

Definition read_zone (z:symbolic_zone) :=
  foldr (fun s acc => Sv.union (read_slice s) acc) Sv.empty z.

Definition wf_vars_zone vars z :=
  Sv.Subset (read_zone z) vars.

Definition wfr_VARS_ZONE vars rmap :=
  forall x sr,
    Mvar.get rmap.(var_region) x = Some sr ->
    wf_vars_zone vars sr.(sr_zone).

Definition read_interval (i:intervals) :=
  foldr (fun s acc => Sv.union (read_slice s) acc) Sv.empty i.

Definition wf_vars_interval vars i :=
  Sv.Subset (read_interval i) vars.

Definition wf_vars_status vars status :=
  match status with
  | Borrowed i => wf_vars_interval vars i
  | _ => True
  end.

Definition wfr_VARS_STATUS vars rv :=
  forall r x, wf_vars_status vars (get_var_status rv r x).

(* A well-formed interval can be associated to a concrete interval. *)
Definition wf_interval vme i := exists ci, mapM (sem_slice vme) i = ok ci.

Definition wf_status vme status :=
  match status with
  | Borrowed i => wf_interval vme i
  | _ => True
  end.

Definition wfr_STATUS rv vme :=
  forall r x, wf_status vme (get_var_status rv r x).

(* This allows to read uniformly in words and arrays. *)
Definition get_val_byte v off :=
  match v with
  | Vword ws w =>
    if ((0 <=? off) && (off <? wsize_size ws)) then ok (LE.wread8 w off)
    else Error ErrOob
  | Varr _ a => read a Aligned off U8
  |_ => type_error
  end.

Definition sub_region_addr vme sr :=
  Let cs := sem_zone vme sr.(sr_zone) in
  ok (Addr sr.(sr_region).(r_slot) + wrepr _ cs.(cs_ofs))%R.

Definition offset_in_concrete_slice cs off :=
  ((cs.(cs_ofs) <=? off) && (off <? cs.(cs_ofs) + cs.(cs_len)))%Z.

(* "concrete interval" is just [seq concrete_slice] *)
Definition offset_in_concrete_interval ci off :=
  has (fun cs => offset_in_concrete_slice cs off) ci.

Definition valid_offset_interval vme i off :=
  forall ci,
    mapM (sem_slice vme) i = ok ci ->
    ~ offset_in_concrete_interval ci off.

Definition valid_offset vme status off : Prop :=
  match status with
  | Valid => true
  | Unknown => false
  | Borrowed i => valid_offset_interval vme i off
  end.

Definition eq_sub_region_val_read vme (m2:mem) sr status v :=
  forall off ofs w,
     sub_region_addr vme sr = ok ofs ->
     valid_offset vme status off ->
     get_val_byte v off = ok w ->
     read m2 Aligned (ofs + wrepr _ off)%R U8 = ok w.

Definition eq_sub_region_val ty vme m2 sr status v :=
  eq_sub_region_val_read vme m2 sr status v /\
  (* According to the psem semantics, a variable of type [sword ws] can store
     a value of type [sword ws'] of shorter size (ws' <= ws).
     But actually, this is used only for register variables.
     For stack variables, we check in [alloc_lval] in stack_alloc.v that the
     value has the same size as the variable, and we remember that fact here.
  *)
  (* Actually, it is handful to know that [ty] and [type_of_val v] are the same
     even in the non-word cases.
  *)
  type_of_val v = ty.

Variable (P: uprog) (ev: @extra_val_t progUnit).
Notation gd := (p_globs P).

(* TODO: could we have this in stack_alloc.v ?
   -> could be used in check_valid/set_arr_word...
   This could mean useless checks for globals, but maybe worth it
   cf. check_vpk_word ?
   Not clear : one advantage of using vpk is to avoid two calls to
   pmap.(globals) and pmap.(locals)
   Could pmap.(globlals) and pmap.(locals) directly return sub_regions ?
*)
Definition check_gvalid rmap x : option (sub_region * status) :=
  if is_glob x then 
    omap (fun '(_, ws) =>
      let sr := sub_region_glob x.(gv) ws in
      let status := Valid in
      (sr, status)) (Mvar.get pmap.(globals) (gv x))
  else
    let sr := Mvar.get rmap.(var_region) x.(gv) in
    match sr with
    | Some sr =>
      let status := get_var_status rmap.(region_var) sr.(sr_region) x.(gv) in
      Some (sr, status)
    | _ => None
    end.

Definition wfr_VAL (rmap:region_map) vme (s1:estate) (s2:estate) :=
  forall x sr status v,
    check_gvalid rmap x = Some (sr, status) ->
    get_gvar true gd s1.(evm) x = ok v ->
    eq_sub_region_val x.(gv).(vtype) vme s2.(emem) sr status v.

Definition valid_pk rmap vme (s2:estate) sr pk : Prop :=
  match pk with
  | Pdirect s ofs ws cs sc =>
    sr = sub_region_direct s ws cs sc
  | Pstkptr s ofs ws cs f =>
    check_stack_ptr rmap s ws cs f ->
    forall pofs ofs,
    sub_region_addr vme (sub_region_stkptr s ws cs) = ok pofs ->
    sub_region_addr vme sr = ok ofs ->
    read s2.(emem) Aligned pofs Uptr = ok ofs
  | Pregptr p =>
    forall ofs, sub_region_addr vme sr = ok ofs ->
    s2.(evm).[p] = Vword ofs
  end.

Definition wfr_PTR (rmap:region_map) vme (s2:estate) :=
  forall x sr, Mvar.get (var_region rmap) x = Some sr ->
    exists pk, get_local pmap x = Some pk /\ valid_pk rmap vme s2 sr pk.

Class wf_rmap vars (rmap:region_map) vme (s1:estate) (s2:estate) := {
  wfr_wf  : wfr_WF rmap vme;
    (* sub-regions in [rmap] are well-formed *)
  wfr_status : wfr_STATUS rmap vme;
    (* statuses in [rmap] are well-formed *)
  wfr_vars_zone : wfr_VARS_ZONE vars rmap;
  wfr_vars_status : wfr_VARS_STATUS vars rmap;
(*   wfr_always : wfr_ALWAYS rmap; *)
  wfr_val : wfr_VAL rmap vme s1 s2;
    (* [rmap] remembers for each relevant program variable which part of the target
       memory contains the value that this variable has in the source. These pieces
       of memory can be safely read without breaking semantics preservation.
    *)
  wfr_ptr : wfr_PTR rmap vme s2;
    (* a variable in [rmap] is also in [pmap] and there is a link between
       the values associated to this variable in both maps *)
}.

Definition eq_mem_source (m1 m2:mem) :=
  forall w, validw m1 Aligned w U8 -> read m1 Aligned w U8 = read m2 Aligned w U8.

Hypothesis wf_pmap0 : wf_pmap.

(* FIXME: could we put [m0] as section variable? it should not be modified? *)
(* [m0]: initial target memory (just before the call to the current function)
   [s1]: current source estate
   [s2]: current target estate
*)
Class valid_state table (rmap : region_map) vme (m0 : mem) (s1 s2 : estate) := {
  vs_scs         : s1.(escs) = s2.(escs);
  vs_slot_valid  : slot_valid s2.(emem);
    (* slots are valid in the target *)
  vs_disjoint    : disjoint_source s1.(emem);
    (* slots are disjoint from the source memory *)
  vs_valid_incl  : valid_incl s1.(emem) s2.(emem);
    (* every valid memory cell in the source is valid in the target *)
  vs_valid_incl2 : valid_incl m0 s2.(emem);
    (* every valid memory cell before the call is valid during the call *)
  vs_unchanged   : mem_unchanged s1.(emem) m0 s2.(emem);
    (* stack memory (i.e. valid in the target before the call but not in the source)
       disjoint from writable slots is unchanged between [m0] and [s2] *)
  vs_rip         : (evm s2).[pmap.(vrip)] = Vword rip;
    (* [vrip] stores address [rip] *)
  vs_rsp         : (evm s2).[pmap.(vrsp)] = Vword rsp;
    (* [vrsp] stores address [rsp] *)
  vs_eq_vm       : eq_vm s1.(evm) s2.(evm);
    (* registers already present in the source program store the same values
       in the source and in the target *)
  vs_wf_table    : wf_table table vme s1.(evm);
  vs_wf_region   : wf_rmap table.(vars) rmap vme s1 s2;
    (* cf. [wf_rmap] definition *)
  vs_eq_mem      : eq_mem_source s1.(emem) s2.(emem);
    (* the memory that is already valid in the source is the same in the target *)
  vs_glob_valid  : forall p, between rip glob_size p U8 -> validw m0 Aligned p U8;
    (* globals are valid in the target before the call *)
  vs_top_stack   : rsp = top_stack (emem s2);
    (* [rsp] is the stack pointer, it points to the top of the stack *)
}.

Existing Instance vs_wf_region.

(* We extend some predicates with the global case. *)
(* -------------------------------------------------------------------------- *)

Lemma sub_region_glob_wf vme x ofs ws :
  wf_global x ofs ws ->
  wf_sub_region vme (sub_region_glob x ws) x.(vtype).
Proof.
  move=> [*]; split.
  + by split=> //; apply /idP.
  eexists; first by reflexivity.
  by split=> /=; lia.
Qed.

Lemma check_gvalid_wf rmap vme x sr_status :
  wfr_WF rmap vme ->
  check_gvalid rmap x = Some sr_status ->
  wf_sub_region vme sr_status.1 x.(gv).(vtype).
Proof.
  move=> hwfr.
  rewrite /check_gvalid; case: (@idP (is_glob x)) => hg.
  + by case heq: Mvar.get => [[??]|//] [<-] /=; apply (sub_region_glob_wf vme (wf_globals heq)).
  by case heq: Mvar.get => // -[<-]; apply hwfr.
Qed.

Lemma check_gvalid_wf_status (rmap:region_map) vme x sr_status :
  wfr_STATUS rmap vme ->
  check_gvalid rmap x = Some sr_status ->
  wf_status vme sr_status.2.
Proof.
  move=> hwfs.
  rewrite /check_gvalid; case: (@idP (is_glob x)) => hg.
  + by case heq: Mvar.get => [[??]|//] [<-] /=.
  by case heq: Mvar.get => // -[<-]; apply hwfs.
Qed.

Definition valid_vpk rv vme s2 x sr vpk :=
  match vpk with
  | VKglob (_, ws) => sr = sub_region_glob x ws
  | VKptr pk => valid_pk rv vme s2 sr pk
  end.

Lemma get_globalP x z : get_global pmap x = ok z <-> Mvar.get pmap.(globals) x = Some z.
Proof.
  rewrite /get_global; case: Mvar.get; last by split.
  by move=> ?;split => -[->].
Qed.

(* A variant of [wfr_PTR] for [gvar]. *)
Lemma wfr_gptr vars rmap vme s1 s2 x sr status :
  wf_rmap vars rmap vme s1 s2 ->
  check_gvalid rmap x = Some (sr, status) ->
  exists vpk, get_var_kind pmap x = ok (Some vpk)
  /\ valid_vpk rmap vme s2 x.(gv) sr vpk.
Proof.
  move=> hrmap.
  rewrite /check_gvalid /get_var_kind.
  case: is_glob.
  + case heq: Mvar.get => [[ofs ws]|//] /= [<- _].
    have /get_globalP -> := heq.
    by eexists.
  case heq: Mvar.get => // [sr'] [<- _].
  have /wfr_ptr [pk [-> hpk]] := heq.
  by eexists.
Qed.

(* [wf_global] and [wf_direct] in a single predicate. *)
Definition wf_vpk x vpk :=
  match vpk with
  | VKglob zws => wf_global x zws.1 zws.2
  | VKptr pk => wf_local x pk
  end.

Lemma get_var_kind_wf x vpk :
  get_var_kind pmap x = ok (Some vpk) ->
  wf_vpk x.(gv) vpk.
Proof.
  rewrite /get_var_kind.
  case: is_glob.
  + by t_xrbindP=> -[ofs ws] /get_globalP /wf_globals ? <-.
  case heq: get_local => [pk|//] [<-].
  by apply wf_locals.
Qed.

(* Predicates about concrete slices: zbetween, disjoint *)
(* -------------------------------------------------------------------------- *)

Definition zbetween_concrete_slice cs1 cs2 :=
  (cs1.(cs_ofs) <=? cs2.(cs_ofs)) &&
  (cs2.(cs_ofs) + cs2.(cs_len) <=? cs1.(cs_ofs) + cs1.(cs_len)).

Lemma zbetween_concrete_sliceP cs1 cs2 off :
  zbetween_concrete_slice cs1 cs2 ->
  offset_in_concrete_slice cs2 off ->
  offset_in_concrete_slice cs1 off.
Proof.
  rewrite /zbetween_concrete_slice /offset_in_concrete_slice !zify.
  by lia.
Qed.

Lemma zbetween_concrete_slice_refl cs : zbetween_concrete_slice cs cs.
Proof. by rewrite /zbetween_concrete_slice !zify; lia. Qed.

Lemma zbetween_concrete_slice_trans z1 z2 z3 :
  zbetween_concrete_slice z1 z2 ->
  zbetween_concrete_slice z2 z3 ->
  zbetween_concrete_slice z1 z3.
Proof. by rewrite /zbetween_concrete_slice !zify; lia. Qed.

Lemma sub_concrete_slice_incl cs1 cs2 cs :
  sub_concrete_slice cs1 cs2 = ok cs ->
  zbetween_concrete_slice cs1 cs.
Proof.
  rewrite /sub_concrete_slice /zbetween_concrete_slice.
  case: ifP => // + [<-] /=.
  rewrite !zify.
  by lia.
Qed.

Definition disjoint_concrete_slice cs1 cs2 :=
  (cs1.(cs_ofs) + cs1.(cs_len) <=? cs2.(cs_ofs)) ||
  (cs2.(cs_ofs) + cs2.(cs_len) <=? cs1.(cs_ofs)).

Lemma disjoint_concrete_sliceP cs1 cs2 off :
  disjoint_concrete_slice cs1 cs2 ->
  offset_in_concrete_slice cs1 off ->
  offset_in_concrete_slice cs2 off ->
  False.
Proof.
  rewrite /disjoint_concrete_slice /offset_in_concrete_slice !zify.
  by lia.
Qed.

Lemma disjoint_concrete_slice_sym cs1 cs2 :
  disjoint_concrete_slice cs1 cs2 = disjoint_concrete_slice cs2 cs1.
Proof. by rewrite /disjoint_concrete_slice orbC. Qed.

Lemma disjoint_concrete_slice_incl cs1 cs1' cs2 cs2' :
  zbetween_concrete_slice cs1 cs1' ->
  zbetween_concrete_slice cs2 cs2' ->
  disjoint_concrete_slice cs1 cs2 ->
  disjoint_concrete_slice cs1' cs2'.
Proof.
  by rewrite /zbetween_concrete_slice /disjoint_concrete_slice !zify; lia.
Qed.

Lemma disjoint_concrete_slice_incl_l cs1 cs1' cs2 :
  zbetween_concrete_slice cs1 cs1' ->
  disjoint_concrete_slice cs1 cs2 ->
  disjoint_concrete_slice cs1' cs2.
Proof.
  move=> ?; apply disjoint_concrete_slice_incl => //.
  by apply zbetween_concrete_slice_refl.
Qed.

Lemma disjoint_concrete_slice_r cs1 cs2 cs2' :
  zbetween_concrete_slice cs2 cs2' ->
  disjoint_concrete_slice cs1 cs2 ->
  disjoint_concrete_slice cs1 cs2'.
Proof.
  move=> ?; apply disjoint_concrete_slice_incl => //.
  by apply zbetween_concrete_slice_refl.
Qed.

Lemma sub_concrete_slice_disjoint cs cs1 cs1' cs2 cs2' :
  sub_concrete_slice cs cs1 = ok cs1' ->
  sub_concrete_slice cs cs2 = ok cs2' ->
  disjoint_concrete_slice cs1 cs2 ->
  disjoint_concrete_slice cs1' cs2'.
Proof.
  rewrite /sub_concrete_slice /disjoint_concrete_slice.
  case: ifP => // _ [<-] /=.
  case: ifP => // _ [<-] /=.
  rewrite !zify.
  by lia.
Qed.


(* Lemmas about sem_zone *)
(* -------------------------------------------------------------------------- *)

Lemma sem_zone_aux_app vme cs z1 cs1 z2 :
  sem_zone_aux vme cs z1 = ok cs1 ->
  sem_zone_aux vme cs (z1 ++ z2) = sem_zone_aux vme cs1 z2.
Proof.
  elim: z1 cs => [|s1 z1 ih1] cs /=.
  + by move=> [<-].
  by t_xrbindP=> cs1' -> /= cs1'' -> /= /ih1.
Qed.

Lemma sem_zone_app vme z1 z2 cs1 :
  sem_zone vme z1 = ok cs1 ->
  sem_zone vme (z1 ++ z2) = sem_zone_aux vme cs1 z2.
Proof.
  case: z1 => [//|s1 z1] /=.
  t_xrbindP=> cs -> /=.
  by apply sem_zone_aux_app.
Qed.

Lemma sub_concrete_slice_assoc cs1 cs2 cs3 cs4 cs5 :
  sub_concrete_slice cs1 cs2 = ok cs3 ->
  sub_concrete_slice cs3 cs4 = ok cs5 ->
  exists2 cs,
    sub_concrete_slice cs2 cs4 = ok cs &
    sub_concrete_slice cs1 cs = ok cs5.
Proof.
  rewrite /sub_concrete_slice.
  case: ifP => // hle1 [<-] /=.
  case: ifP => // hle2 [<-] /=.
  eexists; first by reflexivity.
  move=> /=; case: ifPn; last first.
  + move: hle1 hle2; rewrite !zify.
    by lia.
  by move=> _; rewrite Z.add_assoc.
Qed.

Lemma sem_zone_aux_sub_concrete_slice vme z cs1 cs1' cs cs2 :
  sem_zone_aux vme cs1 z = ok cs1' ->
  sub_concrete_slice cs cs2 = ok cs1 ->
  exists2 cs2',
    sem_zone_aux vme cs2 z = ok cs2' &
    sub_concrete_slice cs cs2' = ok cs1'.
Proof.
  elim: z cs1 cs2 => [|s z ih] cs1 cs2 /=.
  + move=> [<-] ok_cs1.
    by eexists; first by reflexivity.
  t_xrbindP=> ? -> /= cs1'' ok_cs1'' ok_cs1' ok_cs1.
  have [? -> /= hsub] := sub_concrete_slice_assoc ok_cs1 ok_cs1''.
  by apply: ih hsub.
Qed.

Lemma sem_zone_aux_sem_zone vme z cs1 cs2 :
  z <> [::] ->
  sem_zone_aux vme cs1 z = ok cs2 ->
  exists2 cs,
    sem_zone vme z = ok cs &
    sub_concrete_slice cs1 cs = ok cs2.
Proof.
  case: z => [//|s z] _ /=.
  t_xrbindP=> ? -> /= cs1' ok_cs1' ok_cs2.
  by apply (sem_zone_aux_sub_concrete_slice ok_cs2 ok_cs1').
Qed.

Lemma sem_zone_aux_incl vme z cs1 cs2 :
  sem_zone_aux vme cs1 z = ok cs2 ->
  zbetween_concrete_slice cs1 cs2.
Proof.
  elim: z cs1 => [|s z ih] cs1 /=.
  + by move=> [<-]; apply zbetween_concrete_slice_refl.
  t_xrbindP=> cs ok_cs cs1' ok_cs1' ok_cs2.
  apply (zbetween_concrete_slice_trans (sub_concrete_slice_incl ok_cs1')).
  by apply (ih _ ok_cs2).
Qed.

Lemma sem_zone_cons_incl vme s z cs :
  sem_zone vme (s::z) = ok cs ->
  exists2 cs',
    sem_slice vme s = ok cs' & zbetween_concrete_slice cs' cs.
Proof.
  move=> /=.
  t_xrbindP=> ? -> /= ok_cs.
  eexists; first by reflexivity.
  by apply (sem_zone_aux_incl ok_cs).
Qed.

Lemma sem_zone_aux_app_inv vme cs z1 z2 cs2 :
  sem_zone_aux vme cs (z1 ++ z2) = ok cs2 ->
  exists2 cs1,
    sem_zone_aux vme cs z1 = ok cs1 &
    sem_zone_aux vme cs1 z2 = ok cs2.
Proof.
  elim: z1 cs => [|s1 z1 ih1] cs /=.
  + by move=> ?; eexists; first by reflexivity.
  t_xrbindP=> ? -> /= ? -> /= ok_cs2.
  by apply ih1.
Qed.

Lemma sem_zone_app_inv vme z1 z2 cs :
  z1 <> [::] -> z2 <> [::] ->
  sem_zone vme (z1 ++ z2) = ok cs ->
  exists cs1 cs2, [/\
    sem_zone vme z1 = ok cs1,
    sem_zone vme z2 = ok cs2 &
    sub_concrete_slice cs1 cs2 = ok cs].
Proof.
  case: z1 => [//|s1 z1] _ /=.
  move=> z2_nnil.
  t_xrbindP=> cs1 -> /= ok_cs.
  have [{}cs1 -> /= {}ok_cs] := sem_zone_aux_app_inv ok_cs.
  have [cs2 ok_cs2 {}ok_cs] := sem_zone_aux_sem_zone z2_nnil ok_cs.
  by exists cs1, cs2.
Qed.

(* Lemmas about wf_zone *)
(* -------------------------------------------------------------------------- *)

Lemma wf_concrete_slice_len_gt0 cs ty sl :
  wf_concrete_slice cs ty sl -> 0 < cs.(cs_len).
Proof. by move=> [? _]; have := size_of_gt0 ty; lia. Qed.

(* Lemmas about wf_sub_region *)
(* -------------------------------------------------------------------------- *)

(* TODO: move this closer to alloc_array_moveP? Before, this was used everywhere
   but not anymore. *)

Lemma wf_sub_region_size_of vme sr ty1 ty2 :
  size_of ty2 <= size_of ty1 ->
  wf_sub_region vme sr ty1 ->
  wf_sub_region vme sr ty2.
Proof.
  move=> hle [hwf1 hwf2]; split=> //.
  case: hwf2 => cs ok_cs [wf_cs1 wf_cs2].
  exists cs => //; split=> //.
  by lia.
Qed.

Lemma wf_sub_region_subtype vme sr ty1 ty2 :
  subtype ty2 ty1 ->
  wf_sub_region vme sr ty1 ->
  wf_sub_region vme sr ty2.
Proof.
  move=> hsub hwf.
  by apply (wf_sub_region_size_of (size_of_le hsub) hwf).
Qed.

Lemma split_lastP z z' s :
  z <> [::] ->
  split_last z = (z', s) ->
  z = z' ++ [:: s].
Proof.
  elim: z z' => [//|s1 z1 ih1] z' _ /=.
  case: z1 ih1 => [|s1' z1] ih1.
  + by move=> [<- <-].
  case hsplit: split_last => [z last].
  move=> [??]; subst z' s.
  by rewrite (ih1 _ ltac:(discriminate) hsplit).
Qed.

Lemma sub_concrete_slice_wf cs ty sl ofs ty2 :
  wf_concrete_slice cs ty sl ->
  0 <= ofs /\ ofs + size_of ty2 <= size_of ty ->
  exists2 cs',
    sub_concrete_slice cs {| cs_ofs := ofs; cs_len := size_of ty2 |} = ok cs' &
    wf_concrete_slice cs' ty2 sl.
Proof.
  move=> [wf_len wf_ofs] hofs.
  rewrite /sub_concrete_slice /=.
  case: ifPn.
  + move=> _.
    eexists; split; first by reflexivity.
    move=> /=.
    by lia.
  rewrite !zify.
  by lia.
Qed.

Variant is_reflect A (P0 : A -> sexpr) : sexpr -> option A -> Prop :=
| Is_reflect_some : forall a, is_reflect (P0 a) (Some a)
| Is_reflect_none : forall e, is_reflect e None.

Lemma is_constP e : is_reflect Sconst e (is_const e).
Proof. by case: e => /= *; constructor. Qed.

Lemma sub_zone_at_ofsP vme z cs ty sl ofs ofsi ty2 :
  sem_zone vme z = ok cs ->
  wf_concrete_slice cs ty sl ->
  sem_sexpr vme ofs >>= to_int = ok ofsi ->
  0 <= ofsi /\ ofsi + size_of ty2 <= size_of ty ->
  exists cs', [/\
    sem_zone vme (sub_zone_at_ofs z ofs (Sconst (size_of ty2))) = ok cs',
    wf_concrete_slice cs' ty2 sl &
    sub_concrete_slice cs {| cs_ofs := ofsi; cs_len := size_of ty2 |} = ok cs'].
Proof.
  move=> ok_cs wf_cs ok_ofsi hofsi.
  have [cs' ok_cs' wf_cs'] := sub_concrete_slice_wf wf_cs hofsi.
  exists cs'; split=> //.
  rewrite /sub_zone_at_ofs.
  case hsplit: split_last => [z' s].
  have hz: z <> [::].
  + by move=> hnil; rewrite hnil in ok_cs.
  have {}hsplit := split_lastP hz hsplit.
  have hsem:
    sem_zone vme
      (z ++ [:: {| ss_ofs := ofs; ss_len := Sconst (size_of ty2) |}]) = ok cs'.
  + rewrite (sem_zone_app _ ok_cs).
    by rewrite /= /sem_slice /= ok_ofsi /= ok_cs'.
  move: (erefl (sem_slice vme s)); rewrite {2}/sem_slice.
  case: is_constP => [sofs|//].
  case: is_constP => [slen|//] /= hs.
  case: is_constP ok_ofsi hsem => [_|//] /= [->] _.
  rewrite {}hsplit in ok_cs.
  have: z' = [::] \/ z' <> [::].
  + by case: (z'); [left|right].
  case=> [?|z'_nnil].
  + subst z'.
    move: hs ok_cs ok_cs' => /= -> /= [<-].
    rewrite /sub_concrete_slice /=.
    by case: ifP.
  have := sem_zone_app_inv (z2:=[::s]) z'_nnil ltac:(discriminate) ok_cs.
  rewrite /= hs /= => -[cs1 [_ [hz' [<-] hsub]]].
  rewrite (sem_zone_app _ hz') /=.
  have [] := sub_concrete_slice_assoc hsub ok_cs'.
  by rewrite {1}/sub_concrete_slice /=; case: ifP => // _ _ [<-] ->.
Qed.

Lemma read_zone_cat z1 z2 :
  Sv.Equal (read_zone (z1 ++ z2)) (Sv.union (read_zone z1) (read_zone z2)).
Proof.
  elim: z1 => [|s1 z1 ih1] /=.
  + by clear; SvD.fsetdec.
  by clear -ih1; SvD.fsetdec.
Qed.

Lemma sub_zone_at_ofs_wf_vars_zone vars z ofs len :
  wf_vars_zone vars z ->
  Sv.Subset (read_e ofs) vars ->
  Sv.Subset (read_e len) vars ->
  wf_vars_zone vars (sub_zone_at_ofs z ofs len).
Proof.
  move=> z_vars ofs_vars len_vars.
  rewrite /sub_zone_at_ofs.
  have hvars: wf_vars_zone vars (z ++ [:: {| ss_ofs := ofs; ss_len := len |}]).
  + rewrite /wf_vars_zone /= read_zone_cat {2}/read_zone /= /read_slice /=.
    move: z_vars; rewrite /wf_vars_zone.
    by clear -ofs_vars len_vars; SvD.fsetdec.
  have: z = [::] \/ z <> [::].
  + by case: (z); [left|right].
  case=> hz.
  + subst z => /=.
    case: is_const => [zofs|//].
    case: is_const => [zlen|//].
    rewrite /wf_vars_zone /= /read_slice /= /read_e /=.
    by clear; SvD.fsetdec.
  case hsplit: split_last => [z' s].
  case: is_const => [zofs1|//].
  case: is_const => [zlen1|//].
  case: is_const => [zofs|//].
  case: is_const => [zlen|//].
  move: z_vars; rewrite (split_lastP hz hsplit).
  rewrite /wf_vars_zone !read_zone_cat.
  rewrite {4}/read_zone /= {2}/read_slice /= /read_e /=.
  by clear; SvD.fsetdec.
Qed.

Lemma sub_region_at_ofs_wf vme sr ty ofs ofsi ty2 :
  wf_sub_region vme sr ty ->
  sem_sexpr vme ofs >>= to_int = ok ofsi ->
  0 <= ofsi /\ ofsi + size_of ty2 <= size_of ty ->
  wf_sub_region vme (sub_region_at_ofs sr ofs (Sconst (size_of ty2))) ty2.
Proof.
  move=> [hwfr hwfz] ok_ofsi hofsi; split=> //=.
  have [cs ok_cs wf_cs] := hwfz.
  have [cs' [ok_cs' wf_cs' hsub]] := sub_zone_at_ofsP ok_cs wf_cs ok_ofsi hofsi.
  by exists cs'.
Qed.

Lemma sub_region_addr_offset vme sr ty ofs ofsi ty2 addr :
  wf_sub_region vme sr ty ->
  sem_sexpr vme ofs >>= to_int = ok ofsi ->
  0 <= ofsi /\ ofsi + size_of ty2 <= size_of ty ->
  sub_region_addr vme sr = ok addr ->
  sub_region_addr vme (sub_region_at_ofs sr ofs (Sconst (size_of ty2))) = ok (addr + wrepr _ ofsi)%R.
Proof.
  move=> hwf ok_ofsi hofsi.
  have [cs ok_cs wf_cs] := hwf.(wfsr_zone).
  have [cs' [ok_cs' wf_cs' hsub]] := sub_zone_at_ofsP ok_cs wf_cs ok_ofsi hofsi.
  rewrite /sub_region_addr ok_cs /= => -[<-].
  rewrite ok_cs' /=.
  move: hsub; rewrite /sub_concrete_slice /=.
  case: ifP => // _ [<-] /=.
  by rewrite wrepr_add GRing.addrA.
Qed.

Lemma wf_sub_region_sub_region_addr vme sr ty :
  wf_sub_region vme sr ty ->
  exists w, sub_region_addr vme sr = ok w.
Proof.
  move=> hwf.
  have [cs ok_cs _] := hwf.(wfsr_zone).
  rewrite /sub_region_addr ok_cs /=.
  by eexists; reflexivity.
Qed.

Lemma wunsigned_sub_region_addr vme sr ty cs :
  wf_sub_region vme sr ty ->
  sem_zone vme sr.(sr_zone) = ok cs ->
  exists2 w,
    sub_region_addr vme sr = ok w &
    wunsigned w = wunsigned (Addr sr.(sr_region).(r_slot)) + cs.(cs_ofs).
Proof.
  move=> [hwf [cs2 ok_cs wf_cs]]; rewrite ok_cs => -[?]; subst cs2.
  rewrite /sub_region_addr; rewrite ok_cs /=.
  eexists; first by reflexivity.
  apply wunsigned_add.
  have hlen := wf_concrete_slice_len_gt0 wf_cs.
  have hofs := wfcs_ofs wf_cs.
  have /ZleP hno := addr_no_overflow (wfr_slot hwf).
  have ? := wunsigned_range (Addr (sr.(sr_region).(r_slot))).
  by lia.
Qed.

Lemma zbetween_sub_region_addr vme sr ty ofs :
  wf_sub_region vme sr ty ->
  sub_region_addr vme sr = ok ofs ->
  zbetween (Addr sr.(sr_region).(r_slot)) (size_slot sr.(sr_region).(r_slot))
    ofs (size_of ty).
Proof.
  move=> hwf haddr.
  have [cs ok_cs wf_cs] := hwf.(wfsr_zone).
  have := wunsigned_sub_region_addr hwf ok_cs.
  rewrite haddr => -[_ [<-] heq].
  rewrite /zbetween !zify heq.
  have hofs := wf_cs.(wfcs_ofs).
  have hlen := wf_cs.(wfcs_len).
  by lia.
Qed.

Lemma no_overflow_sub_region_addr vme sr ty ofs :
  wf_sub_region vme sr ty ->
  sub_region_addr vme sr = ok ofs ->
  no_overflow ofs (size_of ty).
Proof.
  move=> hwf haddr.
  apply (no_overflow_incl (zbetween_sub_region_addr hwf haddr)).
  by apply (addr_no_overflow hwf.(wfr_slot)).
Qed.

(* [valid_state]'s clauses deal about U8 only. We show extended versions valid
   for any [ws].
*)
(* -------------------------------------------------------------------------- *)

Lemma valid_incl_word table rmap vme m0 s1 s2 al p ws :
  valid_state table rmap vme m0 s1 s2 ->
  validw s1.(emem) al p ws ->
  validw s2.(emem) al p ws.
Proof.
  move=> hvs /validwP [hal hvalid].
  apply /validwP; split=> //.
  move=> k hk; rewrite (validw8_alignment Aligned); apply: vs_valid_incl.
  rewrite (validw8_alignment al).
  exact: hvalid.
Qed.

Lemma eq_mem_source_word table rmap vme m0 s1 s2 al p ws :
  valid_state table rmap vme m0 s1 s2 ->
  validw s1.(emem) al p ws ->
  read s1.(emem) al p ws = read s2.(emem) al p ws.
Proof.
  move=> hvs /validwP [hal hvalid].
  apply: eq_read => al' k hk.
  rewrite !(read8_alignment Aligned).
  apply: vs_eq_mem.
  rewrite (validw8_alignment al).
  exact: hvalid.
Qed.

(* [eq_sub_region_val_read] deals with 1-byte words. This lemma extends it to
   words of arbitrary sizes, when status is Valid. *)
Lemma eq_sub_region_val_read_word vme sr ty s2 (v : value) ofs ws off w al :
  wf_sub_region vme sr ty ->
  eq_sub_region_val_read vme (emem s2) sr Valid v ->
  sub_region_addr vme sr = ok ofs ->
  (forall k, 0 <= k < wsize_size ws -> get_val_byte v (off + k) = ok (LE.wread8 w k)) ->
  read (emem s2) al (ofs + wrepr _ off)%R ws =
    if is_aligned_if al (ofs + wrepr _ off)%R ws then ok w else Error ErrAddrInvalid.
Proof.
  move=> hwf hread ok_ofs hget.
  apply read8_read.
  move=> al' k hk.
  rewrite addE -GRing.addrA -wrepr_add (read8_alignment Aligned).
  apply hread => //.
  by apply hget.
Qed.

Lemma get_val_byte_word ws (w : word ws) off :
  0 <= off < wsize_size ws ->
  get_val_byte (Vword w) off = ok (LE.wread8 w off).
Proof. by rewrite /= -!zify => ->. Qed.

Lemma get_val_byte_bound v off w :
  get_val_byte v off = ok w -> 0 <= off /\ off < size_val v.
Proof.
  case: v => //.
  + move=> len a /=.
    by rewrite -get_read8 => /WArray.get_valid8 /WArray.in_boundP.
  move=> ws w' /=.
  by case: ifP => //; rewrite !zify.
Qed.

(* -------------------------------------------------------------------------- *)

Lemma check_gvalid_lvar rmap (x : var_i) sr :
  Mvar.get rmap.(var_region) x = Some sr ->
  check_gvalid rmap (mk_lvar x) = Some (sr, get_var_status rmap sr.(sr_region) x).
Proof. by rewrite /check_gvalid /= => ->. Qed.

Lemma check_gvalid_lvar_inv rmap x sr status :
  check_gvalid rmap (mk_lvar x) = Some (sr, status) ->
  Mvar.get rmap.(var_region) x = Some sr /\ status = get_var_status rmap sr.(sr_region) x.
Proof.
  rewrite /check_gvalid /=.
  by case: Mvar.get => [_|//] [-> <-].
Qed.

Lemma check_gvalid_writable rmap x sr status :
  check_gvalid rmap x = Some (sr, status) ->
  sr.(sr_region).(r_writable) ->
  ~ is_glob x.
Proof.
  move=> + + hnglob.
  rewrite /check_gvalid hnglob.
  by case: Mvar.get => [[_ _]|//] /= [<- _] /=.
Qed.

Lemma cast_ptrP wdb gd s e i :
  sem_pexpr wdb gd s e >>= to_int = ok i ->
  exists2 v, sem_pexpr wdb gd s (cast_ptr e) = ok v & value_uincl (Vword (wrepr Uptr i)) v.
Proof.
  t_xrbindP => v he hi.
  apply: cast_wP.
  by rewrite /= he /sem_sop1 /= hi.
Qed.

Lemma mk_ofsP wdb aa sz gd s2 ofs e i :
  sem_pexpr wdb gd s2 e >>= to_int = ok i ->
  sem_pexpr wdb gd s2 (mk_ofs aa sz e ofs) = ok (Vword (wrepr Uptr (i * mk_scale aa sz + ofs)%Z)).
Proof.
  rewrite /mk_ofs; case expr_facts.is_constP => /= [? [->] //| {}e he] /=.
  rewrite /sem_sop2 /=.
  have [_ -> /value_uinclE [ws [w [-> huincl]]]] /= := cast_ptrP he.
  rewrite !truncate_word_u /=.
  rewrite (word_uincl_truncate huincl (truncate_word_u _)) /=.
  by rewrite truncate_word_u /= wrepr_add wrepr_mul GRing.mulrC.
Qed.

Lemma mk_ofs_intP vme e i aa sz :
  sem_sexpr vme e >>= to_int = ok i ->
  sem_sexpr vme (mk_ofs_int aa sz e) = ok (Vint (i * mk_scale aa sz)).
Proof.
  rewrite /mk_ofs_int; case is_constP => /= [? [->] //| {}e he] /=.
  move: he; t_xrbindP => v ok_v ok_i.
  by rewrite ok_v /= /sem_sop2 /= ok_i /= Z.mul_comm.
Qed.

Section EXPR.
  Variables (table : table) (rmap:region_map).
  Variables (vme : Vm.t) (m0:mem) (s:estate) (s':estate).
  Hypothesis (hvalid: valid_state table rmap vme m0 s s').

  (* If [x] is a register, it is not impacted by the presence of global
     variables per hypothesis [vs_eq_vm].
  *)
  Lemma get_var_kindP wdb x v:
    get_var_kind pmap x = ok None ->
    ~ Sv.In x.(gv) pmap.(vnew) ->
    get_gvar wdb gd (evm s) x = ok v ->
    get_gvar wdb [::] (evm s') x = ok v.
  Proof.
    rewrite /get_var_kind; case: ifPn => hglob; first by t_xrbindP.
    case hgl : get_local => // _ /(vs_eq_vm hgl) heq.
    by rewrite !get_gvar_nglob // /get_var heq.
  Qed.

  Lemma base_ptrP sc : (evm s').[base_ptr pmap sc] = Vword (wbase_ptr sc).
  Proof. by case: sc => /=; rewrite (vs_rsp, vs_rip). Qed.

  Lemma Zland_mod z ws : Z.land z (wsize_size ws - 1) = z mod wsize_size ws.
  Proof.
    rewrite wsize_size_is_pow2 -Z.land_ones; last by case: ws.
    by rewrite Z.ones_equiv.
  Qed.

  Lemma divideP ws e i :
    divide e ws ->
    sem_sexpr vme e >>= to_int = ok i ->
    i mod wsize_size ws = 0.
  Proof.
    case: e => //=.
    + move=> z.
      by rewrite /divide_z Zland_mod => /eqP hdiv -[<-].
    move=> opk e1 e2.
    move=> /orP [].
    + case: is_constP => //= z1.
      rewrite /divide_z Zland_mod => /eqP hdiv.
      t_xrbindP=> v v2 ok_v2.
      case: opk => //=.
      rewrite /sem_sop2 /=.
      t_xrbindP=> z2 ok_z2 <- /= [<-].
      by rewrite Zmult_mod hdiv /= Zmod_0_l.
    case: is_constP => //= z2.
    rewrite /divide_z Zland_mod => /eqP hdiv.
    t_xrbindP=> v v1 ok_v1.
    case: opk; last by rewrite /sem_sop2 /=; t_xrbindP.
    rewrite /sem_sop2 /=.
    t_xrbindP=> z1 ok_z1 <- /= [<-].
    by rewrite Zmult_mod hdiv Z.mul_0_r Zmod_0_l.
  Qed.

  Lemma divide_slice sli ws cs :
    divide (ss_ofs sli) ws ->
    sem_slice vme sli = ok cs ->
    cs.(cs_ofs) mod wsize_size ws = 0.
  Proof.
    move=> hdiv.
    rewrite /sem_slice.
    apply: rbindP => ofs ok_ofs.
    apply: rbindP => len _ [<-] /=.
    by apply (divideP hdiv ok_ofs).
  Qed.

  Lemma divide_zone_aux z ws cs cs' :
    divide_zone z ws ->
    sem_zone_aux vme cs z = ok cs' ->
    cs'.(cs_ofs) mod wsize_size ws = cs.(cs_ofs) mod wsize_size ws.
  Proof.
    elim: z cs => [|s1 z ih] cs /=.
    + by move=> _ [<-].
    move=> /andP [hdiv1 hdiv2].
    t_xrbindP=> cs1 ok_cs1.
    rewrite /sub_concrete_slice; case: ifP => // _ _ [<-] ok_cs'.
    rewrite (ih _ hdiv2 ok_cs') /=.
    by rewrite Zplus_mod (divide_slice hdiv1 ok_cs1) Z.add_0_r Zmod_mod.
  Qed.

  Lemma divide_zone z ws cs :
    divide_zone z ws ->
    sem_zone vme z = ok cs ->
    cs.(cs_ofs) mod wsize_size ws = 0.
  Proof.
    case: z => [//|s1 z] /= /andP [hdiv1 hdiv2].
    t_xrbindP=> cs1 ok_cs1 ok_cs.
    rewrite (divide_zone_aux hdiv2 ok_cs).
    by apply (divide_slice hdiv1 ok_cs1).
  Qed.

  Lemma check_alignP x sr ty w al ws tt :
    wf_sub_region vme sr ty ->
    sub_region_addr vme sr = ok w ->
    check_align al x sr ws = ok tt ->
    is_aligned_if al w ws.
  Proof.
    move=> hwf ok_w; rewrite /check_align; t_xrbindP.
    case: al => //= halign halign2.
    have: is_align (Addr sr.(sr_region).(r_slot)) ws.
    + apply (is_align_m halign).
      rewrite -hwf.(wfr_align).
      by apply (slot_align hwf.(wfr_slot)).
    rewrite /is_align !p_to_zE.
    have [cs ok_cs _] := hwf.(wfsr_zone).
    have := wunsigned_sub_region_addr hwf ok_cs.
    rewrite ok_w => -[_ [<-] ->].
    rewrite Z.add_mod //.
    move=> /eqP -> /=.
    by rewrite (divide_zone halign2 ok_cs).
  Qed.

  Lemma get_sub_regionP x sr :
    get_sub_region rmap x = ok sr <-> Mvar.get rmap.(var_region) x = Some sr.
  Proof.
    rewrite /get_sub_region; case: Mvar.get; last by split.
    by move=> ?; split => -[->].
  Qed.

  Lemma get_sub_region_statusP (x : var_i) sr status :
    get_sub_region_status rmap x = ok (sr, status) ->
    Mvar.get rmap.(var_region) x = Some sr
    /\ status = get_var_status rmap sr.(sr_region) x.
  Proof.
    rewrite /get_sub_region_status.
    by t_xrbindP=> ? /get_sub_regionP -> -> ->.
  Qed.

  Lemma is_validP status :
    is_valid status -> status = Valid.
  Proof. by case: status. Qed.

  Lemma check_validP (x : var_i) status tt :
    check_valid x status = ok tt ->
    status = Valid.
  Proof. by rewrite /check_valid; t_xrbindP=> /is_validP. Qed.

  Lemma sub_region_addr_glob x ofs ws :
    wf_global x ofs ws ->
    sub_region_addr vme (sub_region_glob x ws) = ok (rip + wrepr _ ofs)%R.
  Proof.
    by move=> hwf; rewrite /sub_region_addr /= hwf.(wfg_offset) wrepr0 GRing.addr0.
  Qed.

  Lemma sub_region_addr_direct x sl ofs ws cs sc :
    wf_direct x sl ofs ws cs sc ->
    sub_region_addr vme (sub_region_direct sl ws cs sc) =
      ok (wbase_ptr sc + wrepr _ (ofs + cs.(cs_ofs)))%R.
  Proof.
    by move=> hwf; rewrite /sub_region_addr hwf.(wfd_offset) wrepr_add GRing.addrA.
  Qed.

  Lemma sub_region_addr_stkptr x sl ofs ws cs f :
    wf_stkptr x sl ofs ws cs f ->
    sub_region_addr vme (sub_region_stkptr sl ws cs) =
      ok (rsp + wrepr _ (ofs + cs.(cs_ofs)))%R.
  Proof.
    by move=> hwf; rewrite /sub_region_addr /= hwf.(wfs_offset) wrepr_add GRing.addrA.
  Qed.

  Lemma sub_region_stkptr_wf y sl ofs ws cs f :
    wf_stkptr y sl ofs ws cs f ->
    wf_sub_region vme (sub_region_stkptr sl ws cs) spointer.
  Proof.
    case=> *; split=> //.
    by eexists; first by reflexivity.
  Qed.

  Lemma get_gsub_region_statusP x vpk sr status :
    get_var_kind pmap x = ok (Some vpk) ->
    get_gsub_region_status rmap x.(gv) vpk = ok (sr, status) ->
    check_gvalid rmap x = Some (sr, status).
  Proof.
    rewrite /get_var_kind /check_gvalid.
    case : (@idP (is_glob x)) => hg.
    + by t_xrbindP=> -[_ ws'] /get_globalP -> <- /= [<- <-].
    case hlocal: get_local => [pk|//] [<-].
    by move=> /get_sub_region_statusP [-> ->].
  Qed.

  Lemma addr_from_pkP wdb (x:var_i) pk sr ty xi ofs :
    wf_local x pk ->
    valid_pk rmap vme s' sr pk ->
    wf_sub_region vme sr ty ->
    addr_from_pk pmap x pk = ok (xi, ofs) ->
    exists2 w,
      get_var wdb (evm s') xi >>= to_pointer = ok w &
      sub_region_addr vme sr = ok (w + wrepr _ ofs)%R.
  Proof.
    case: pk => //.
    + move=> sl ofs' ws cs sc hwfpk /= -> _ [<- <-].
      rewrite /= /get_var base_ptrP /= orbT /= truncate_word_u.
      eexists; first by reflexivity.
      by apply (sub_region_addr_direct hwfpk).
    move=> p hwfpk /= hpk hwf [<- <-].
    have [w ok_w] := wf_sub_region_sub_region_addr hwf.
    rewrite /= /get_var (hpk _ ok_w) /= orbT /= truncate_word_u.
    eexists; first by reflexivity.
    by rewrite wrepr0 GRing.addr0.
  Qed.

  Lemma addr_from_vpkP wdb (x:var_i) vpk sr ty xi ofs :
    wf_vpk x vpk ->
    valid_vpk rmap vme s' x sr vpk ->
    wf_sub_region vme sr ty ->
    addr_from_vpk pmap x vpk = ok (xi, ofs) ->
    exists2 w,
      get_var wdb (evm s') xi >>= to_pointer = ok w &
      sub_region_addr vme sr = ok (w + wrepr _ ofs)%R.
  Proof.
    case: vpk => [[ofs' ws]|pk].
    + move=> hwfpk /= -> hwf [<- <-].
      rewrite /= /get_var vs_rip /= orbT /= truncate_word_u.
      eexists; first by reflexivity.
      by rewrite (sub_region_addr_glob hwfpk).
    by apply addr_from_pkP.
  Qed.

  Let X e : Prop :=
    ∀ ty e' v v2,
      alloc_e pmap rmap e ty = ok e' →
      sem_pexpr true gd s e = ok v →
      truncate_val ty v = ok v2 ->
      exists v', sem_pexpr true [::] s' e' = ok v' /\ truncate_val ty v' = ok v2.

  Let Y es : Prop :=
    ∀ err tys es' vs vs2,
      alloc_es pmap rmap es tys = ok es' →
      sem_pexprs true gd s es = ok vs →
      mapM2 err truncate_val tys vs = ok vs2 ->
      exists vs', sem_pexprs true [::] s' es' = ok vs' /\ mapM2 err truncate_val tys vs' = ok vs2.

  Lemma check_varP (x:var_i) t: 
    check_var pmap x = ok t -> 
    get_var_kind pmap (mk_lvar x) = ok None.
  Proof. by rewrite /check_var /get_var_kind /=; case: get_local. Qed.

  Lemma get_gvar_word x ws gd vm v :
    x.(gv).(vtype) = sword ws ->
    get_gvar true gd vm x = ok v ->
    exists (ws' : wsize) (w : word ws'), (ws' <= ws)%CMP /\ v = Vword w.
  Proof.
    move=> hty hget.
    have := type_of_get_gvar hget; rewrite hty => /compat_type_subtype /subtypeE [ws' [hty' hsub]].
    case/type_of_valI: hty' => [? | [w ?]]; subst.
    + by have := get_gvar_undef hget erefl.
    by exists ws', w.
  Qed.

  Lemma check_diffP x t : check_diff pmap x = ok t -> ~Sv.In x (vnew pmap).
  Proof. by rewrite /check_diff; case:ifPn => /Sv_memP. Qed.

  (* Not sure at all if this is the right way to do the proof. *)
  Lemma wbit_subword (ws ws' : wsize) i (w : word ws) k :
    wbit_n (word.subword i ws' w) k = (k < ws')%nat && wbit_n w (k + i).
  Proof.
    clear.
    rewrite /wbit_n.
    case: ltP.
    + move=> /ltP hlt.
      by rewrite word.subwordE word.wbit_t2wE (nth_map ord0) ?size_enum_ord // nth_enum_ord.
    rewrite /nat_of_wsize => hle.
    rewrite word.wbit_word_ovf //.
    by apply /ltP; lia.
  Qed.

  (* TODO: is this result generic enough to be elsewhere ? *)
  Lemma zero_extend_wread8 (ws ws' : wsize) (w : word ws) :
    (ws' <= ws)%CMP ->
    forall off,
      0 <= off < wsize_size ws' ->
      LE.wread8 (zero_extend ws' w) off = LE.wread8 w off.
  Proof.
    clear.
    move=> /wsize_size_le /(Z.divide_pos_le _ _ (wsize_size_pos _)) hle off hoff.
    rewrite /LE.wread8 /LE.encode /split_vec.
    have hmod: forall (ws:wsize), ws %% U8 = 0%nat.
    + by move=> [].
    have hdiv: forall (ws:wsize), ws %/ U8 = Z.to_nat (wsize_size ws).
    + by move=> [].
    have hlt: (Z.to_nat off < Z.to_nat (wsize_size ws))%nat.
    + by apply /ltP /Z2Nat.inj_lt; lia.
    have hlt': (Z.to_nat off < Z.to_nat (wsize_size ws'))%nat.
    + by apply /ltP /Z2Nat.inj_lt; lia.
    rewrite !hmod !addn0.
    rewrite !(nth_map 0%nat) ?size_iota ?hdiv // !nth_iota // !add0n.
    apply /eqP/eq_from_wbit_n => i.
    rewrite !wbit_subword; f_equal.
    rewrite wbit_zero_extend.
    have -> //: (i + Z.to_nat off * U8 <= wsize_size_minus_1 ws')%nat.
    rewrite -ltnS -/(nat_of_wsize ws').
    apply /ltP.
    have := ltn_ord i; rewrite -/(nat_of_wsize _) => /ltP hi.
    have /ltP ? := hlt'.
    have <-: (Z.to_nat (wsize_size ws') * U8 = ws')%nat.
    + by case: (ws').
    by rewrite -!multE -!plusE; nia.
  Qed.

  Lemma check_e_esP : (∀ e, X e) * (∀ es, Y es).
  Proof.
    apply: pexprs_ind_pair; subst X Y; split => //=.
    + move=> err [|//] _ _ _ /= [<-] [<-] [<-].
      by exists [::].
    + move=> e he es hes err [//|ty tys].
      t_xrbindP=> _ _ vs2 e' ok_e' es' ok_es' <- v ok_v vs ok_vs <- /=.
      t_xrbindP=> v2 ok_v2 {}vs2 ok_vs2 <-.
      have [v' [ok_v' htr]] := he _ _ _ _ ok_e' ok_v ok_v2.
      have [vs' [ok_vs' htrs]] := hes _ _ _ _ _ ok_es' ok_vs ok_vs2.
      rewrite ok_v' ok_vs' /=.
      eexists; split; first by reflexivity.
      by rewrite /= htr htrs.
    + move=> z ???? [<-] [<-] /= /truncate_valE [-> ->].
      by eexists; split; first by reflexivity.
    + move=> b ???? [<-] [<-] /= /truncate_valE [-> ->].
      by eexists; split; first by reflexivity.
    + move=> n ???? [<-] [<-] /= /truncate_valE [-> ->].
      eexists; split; first by reflexivity.
      by rewrite /truncate_val /= WArray.castK /=.
    + move=> x ty e' v v2; t_xrbindP => -[ vpk | ] hgvk; last first.
      + t_xrbindP=> /check_diffP hnnew <- /= ok_v htr.
        exists v; split=> //.
        by apply: get_var_kindP.
      case hty: is_word_type => [ws | //]; move /is_word_typeP in hty; subst.
      case: ifP => //; rewrite -/(subtype (sword _) _) => hsub.
      t_xrbindP=> -[sr status] hgsub.
      t_xrbindP=> hcvalid halign [xi ofsi] haddr [<-] hget /= htr.
      have hgvalid := get_gsub_region_statusP hgvk hgsub.
      have hwf := [elaborate check_gvalid_wf wfr_wf hgvalid].
      have hvpk: valid_vpk rmap vme s' x.(gv) sr vpk.
      + have /wfr_gptr := hgvalid.
        by rewrite hgvk => -[_ [[]] <-].
      have [wi ok_wi eq_addr] :=
        addr_from_vpkP true (get_var_kind_wf hgvk) hvpk hwf haddr.
      rewrite ok_wi /= truncate_word_u /=.
      have [ws' [htyx hcmp]] := subtypeEl hsub.
      assert (heq := wfr_val hgvalid hget); rewrite htyx in heq.
      case: heq => hread hty'.
      have [ws'' [w [_ ?]]] := get_gvar_word htyx hget; subst v.
      case: hty' => ?; subst ws''.
      have ? := check_validP hcvalid; subst status.
      rewrite -(GRing.addr0 (_+_)%R) -wrepr0.
      rewrite (eq_sub_region_val_read_word _ hwf hread eq_addr (w:=zero_extend ws w)).
      + rewrite wrepr0 GRing.addr0.
        rewrite (check_alignP hwf eq_addr halign) /=.
        eexists; split; first by reflexivity.
        move: htr; rewrite /truncate_val /=.
        t_xrbindP=> ? /truncate_wordP [_ ->] <-.
        by rewrite truncate_word_u.
      move=> k hk.
      rewrite zero_extend_wread8 //.
      apply (get_val_byte_word w).
      by have /= := size_of_le hsub; rewrite htyx /=; lia.
    + move=> al aa sz x e1 he1 ty e' v v2 he'; apply: on_arr_gvarP => n t htyx /= hget.
      t_xrbindP => i vi /he1{}he1 hvi w hw <- htr.
      exists (Vword w); split=> //.
      move: he'; t_xrbindP => e1' /he1{he1}.
      rewrite /truncate_val /= hvi /= => /(_ _ erefl) [] v' [] he1'.
      t_xrbindP=> i' hv' ?; subst i'.
      have h0 : sem_pexpr true [::] s' e1' >>= to_int = ok i.
      + by rewrite he1' /= hv'.
      move=> [vpk | ]; last first.
      + t_xrbindP => h /check_diffP h1 <- /=.
        by rewrite (get_var_kindP h h1 hget) /= h0 /= hw.
      t_xrbindP=> hgvk [sr status] hgsub.
      t_xrbindP=> hcvalid halign [xi ofsi] haddr [<-] /=.
      have hgvalid := get_gsub_region_statusP hgvk hgsub.
      have hwf := [elaborate check_gvalid_wf wfr_wf hgvalid].
      have hvpk: valid_vpk rmap vme s' x.(gv) sr vpk.
      + have /wfr_gptr := hgvalid.
        by rewrite hgvk => -[_ [[]] <-].
      have [wi ok_wi eq_addr] :=
        addr_from_vpkP true (get_var_kind_wf hgvk) hvpk hwf haddr.
      rewrite ok_wi /= (mk_ofsP aa sz ofsi h0) /= truncate_word_u /=.
      assert (heq := wfr_val hgvalid hget).
      case: heq => hread _.
      have ? := check_validP hcvalid; subst status.
      rewrite wrepr_add (GRing.addrC (wrepr _ _)) GRing.addrA.
      rewrite (eq_sub_region_val_read_word _ hwf hread eq_addr (w:=w)).
      + case: al hw halign => //= hw halign.
        have {}halign := check_alignP hwf eq_addr halign.
        rewrite (is_align_addE halign) WArray.arr_is_align.
        by have [_ _ /= ->] := WArray.get_bound hw.
      have [_ hread8] := (read_read8 hw).
      by move => k hk; rewrite /= (read8_alignment al) -hread8.
    + move=> al1 sz1 v1 e1 IH ty e2 v v2.
      t_xrbindP => /check_varP hc /check_diffP hnnew e1' /IH hrec <- wv1 vv1 /= hget hto' we1 ve1.
      move=> he1 hto wr hr ? htr; subst v.
      exists (Vword wr); split=> //.
      have := hrec _ _ he1.
      rewrite /truncate_val /= hto /= => /(_ _ erefl) [] v' [] he1'.
      t_xrbindP=> w hv' ?; subst w.
      have := get_var_kindP hc hnnew hget; rewrite /get_gvar /= => -> /=.
      rewrite hto' /= he1' /= hv' /=.
      by rewrite -(eq_mem_source_word hvalid (readV hr)) hr.
    + move=> o1 e1 IH ty e2 v v2.
      t_xrbindP => e1' /IH hrec <- ve1 /hrec{}hrec hve1 htr.
      exists v; split=> //=.
      have [ve1' [htr' hve1']] := sem_sop1_truncate_val hve1.
      have [v' [he1' /truncate_value_uincl huincl]] := hrec _ htr'.
      rewrite he1' /=.
      by apply (vuincl_sem_sop1 huincl).
    + move=> o2 e1 H1 e2 H2 ty e' v v2.
      t_xrbindP => e1' /H1 hrec1 e2' /H2 hrec2 <- ve1 /hrec1{}hrec1 ve2 /hrec2{}hrec2 ho2 htr.
      exists v; split=> //=.
      have [ve1' [ve2' [htr1 htr2 ho2']]] := sem_sop2_truncate_val ho2.
      have [v1' [-> /truncate_value_uincl huincl1]] := hrec1 _ htr1.
      have [v2' [-> /truncate_value_uincl huincl2]] := hrec2 _ htr2.
      by rewrite /= (vuincl_sem_sop2 huincl1 huincl2 ho2').
    + move => o es1 H1 ty e2 v v2.
      t_xrbindP => es1' /H1{}H1 <- ves /H1{}H1 /= hves htr.
      exists v; split=> //.
      rewrite -/(sem_pexprs _ _ _ _).
      have [ves' [htr' hves']] := sem_opN_truncate_val hves.
      have [vs' [-> /mapM2_truncate_value_uincl huincl]] := H1 _ _ htr'.
      by rewrite /= (vuincl_sem_opN huincl hves').
    move=> t e He e1 H1 e2 H2 ty e' v v2.
    t_xrbindP=> e_ /He he e1_ /H1 hrec1 e2_ /H2 hrec2 <-.
    move=> b vb /he{}he hvb ve1 ve1' /hrec1{}hrec1 htr1 ve2 ve2' /hrec2{}hrec2 htr2 <- htr.
    move: he; rewrite {1 2}/truncate_val /= hvb /= => /(_ _ erefl) [] vb' [] -> /=.
    t_xrbindP=> b' -> ? /=; subst b'.
    have hsub: subtype ty t.
    + have := truncate_val_subtype htr.
      rewrite fun_if.
      rewrite (truncate_val_has_type htr1) (truncate_val_has_type htr2).
      by rewrite if_same.
    have [ve1'' htr1''] := subtype_truncate_val hsub htr1.
    have := subtype_truncate_val_idem hsub htr1 htr1''.
    move=> /hrec1 [ve1_ [-> /= ->]] /=.
    have [ve2'' htr2''] := subtype_truncate_val hsub htr2.
    have := subtype_truncate_val_idem hsub htr2 htr2''.
    move=> /hrec2 [ve2_ [-> /= ->]] /=.
    eexists; split; first by reflexivity.
    move: htr.
    rewrite !(fun_if (truncate_val ty)).
    rewrite htr1'' htr2''.
    by rewrite (truncate_val_idem htr1'') (truncate_val_idem htr2'').
  Qed.

  Definition alloc_eP := check_e_esP.1.
  Definition alloc_esP := check_e_esP.2.

End EXPR.

Lemma get_localn_checkg_diff rmap sr_status vme s2 x y :
  get_local pmap x = None ->
  wfr_PTR rmap vme s2 ->
  check_gvalid rmap y = Some sr_status ->
  (~is_glob y -> x <> (gv y)).
Proof.
  rewrite /check_gvalid; case:is_glob => // hl hwf.
  case heq: Mvar.get => [sr' | // ] _ _.
  by have /hwf [pk [hy _]] := heq; congruence.
Qed.

Section CLONE.

Variable (clone : (var → PrimInt63.int → var)).
Context (clone_ty : forall x n, (clone x n).(vtype) = x.(vtype)).

Notation symbolic_of_pexpr := (symbolic_of_pexpr clone).
Notation get_symbolic_of_pexpr := (get_symbolic_of_pexpr clone).

Section SYMBOLIC_OF_PEXPR_VARS.

Lemma read_eE e s : Sv.Equal (read_e_rec s e) (Sv.union (read_e e) s).
Proof.
  by elim: e s => [z|x|ws e ih|ws e ih|opk e ih|opk e1 ih1 e2 ih2|opk e1 ih1 e2 ih2|opk e1 ih1 e2 ih2] s;
    rewrite /read_e /= ?ih ?ih2 ?ih1; clear; SvD.fsetdec.
Qed.

Lemma read_e_var (x:var) : Sv.Equal (read_e (Svar x)) (Sv.singleton x).
Proof. by rewrite /read_e /=; clear; SvD.fsetdec. Qed.

Lemma read_esE es s : Sv.Equal (read_es_rec s es) (Sv.union (read_es es) s).
Proof.
  by elim: es s => [|e es ih] s; rewrite /read_es /= ?ih ?read_eE; clear; SvD.fsetdec.
Qed.

Lemma read_es_cons e es :
  Sv.Equal (read_es (e :: es)) (Sv.union (read_e e) (read_es es)).
Proof. by rewrite /read_es /= !read_esE read_eE; clear; SvD.fsetdec. Qed.

Lemma robindP eT aT rT oa (body : aT -> result eT (option rT)) v (P' : Type) :
  (forall z, oa = Some z -> body z = ok (Some v) -> P') ->
  Let%opt a := oa in body a = ok (Some v) ->
  P'.
Proof. by case: oa => // a h h'; exact: (h _ _ h'). Qed.

Lemma symbolic_of_pexpr_varsP table e table' e' :
  symbolic_of_pexpr table e = ok (Some (table', e')) ->
  wft_VARS table -> [/\
    wft_VARS table',
    Sv.Subset table.(vars) table'.(vars) &
    Sv.Subset (read_e e') table'.(vars)].
Proof.
  elim: e table table' e' => //=.
  + move=> z table _ _ [<- <-].
    move=> hvars.
    split=> //.
    rewrite /read_e /=.
    by clear; SvD.fsetdec.
  + move=> x table table' e'.
    case: is_lvar => //.
    t_xrbindP=> -[{}table' {}e'] htable [<- <-].
    move=> hvars.
    move: htable; rewrite /table_get_var.
    case hget: Mvar.get => [e|] /=.
    + move=> [<- <-].
      split=> //.
      by apply: hvars hget.
    rewrite /table_fresh_var.
    t_xrbindP=> /Sv_memP hnin <- <- /=.
    split.
    + move=> y ey /=.
      rewrite Mvar.setP.
      case: eqP => _.
      + move=> [<-].
        rewrite read_e_var.
        by clear; SvD.fsetdec.
      move=> /hvars.
      by clear; SvD.fsetdec.
    + by clear; SvD.fsetdec.
    rewrite read_e_var.
    by clear; SvD.fsetdec.
  + move=> op e he table table' e'.
    apply: robindP => op' ok_op'.
    t_xrbindP=> ote hsym.
    apply: robindP=> -[{}table' {}e'] ? [<- <-]; subst ote.
    move=> hvars.
    have [hvars' hsub hsubr] := he _ _ _ hsym hvars.
    have ->: read_e (op' e') = read_e e'.
    + by case: op ok_op' => // ? [<-].
    by split.
  move=> op e1 he1 e2 he2 table table' e'.
  apply: robindP=> op' ok_op'.
  t_xrbindP=> ote1 hsym1.
  apply: robindP=> -[table1 e1'] ?; subst ote1.
  t_xrbindP=> ote2 hsym2.
  apply: robindP=> -[table2 e2'] ?; subst ote2.
  move=> [<- <-].
  move=> hvars.
  have [hvars1 hsub1 hsubr1] := he1 _ _ _ hsym1 hvars.
  have [hvars2 hsub2 hsubr2] := he2 _ _ _ hsym2 hvars1.
  split=> //.
  + by clear -hsub1 hsub2; SvD.fsetdec.
  have ->: Sv.Equal (read_e (op' e1' e2')) (Sv.union (read_e e1') (read_e e2')).
    + by case: op ok_op' => // ? [<-];
        rewrite /read_e /= -/read_e read_eE; clear; SvD.fsetdec.
    by clear -hsubr1 hsub2 hsubr2; SvD.fsetdec.
Qed.

(* in practice, subsumed by wf_table_symbolic_of_pexpr *)
Lemma wft_VARS_symbolic_of_pexpr table e table' e' :
  symbolic_of_pexpr table e = ok (Some (table', e')) ->
  wft_VARS table ->
  wft_VARS table'.
Proof.
  move=> he hvars.
  by have [hvars' _ _] := symbolic_of_pexpr_varsP he hvars.
Qed.

(* Actually, the hypothesis wft_VARS is not needed, but is was simpler to prove
   the 3 propositions in one go. *)
Lemma symbolic_of_pexpr_subset_vars table e table' e' :
  symbolic_of_pexpr table e = ok (Some (table', e')) ->
  wft_VARS table ->
  Sv.Subset table.(vars) table'.(vars).
Proof.
  move=> he hvars.
  by have [_ hsub _] := symbolic_of_pexpr_varsP he hvars.
Qed.

Lemma symbolic_of_pexpr_subset_read table e table' e' :
  symbolic_of_pexpr table e = ok (Some (table', e')) ->
  wft_VARS table ->
  Sv.Subset (read_e e') table'.(vars).
Proof.
  move=> he hvars.
  by have [_ _ hsubr] := symbolic_of_pexpr_varsP he hvars.
Qed.

End SYMBOLIC_OF_PEXPR_VARS.

Section WF_TABLE_SYMBOLIC_OF_PEXPR.

Context (s : estate).

Lemma sem_sexpr_uincl vme1 vme2 e v1 :
  vme1 <=1 vme2 ->
  sem_sexpr vme1 e = ok v1 ->
  exists2 v2,
    sem_sexpr vme2 e = ok v2 & value_uincl v1 v2.
Proof.
  move=> huincl.
  elim: e v1 => [z|x|ws e ih|ws e ih|opk e ih|opk e1 ih1 e2 ih2|opk e1 ih1 e2 ih2|opk e1 ih1 e2 ih2] v1 /=.
  + move=> [<-].
    by eexists; first by reflexivity.
  + by apply get_var_uincl.
  + t_xrbindP=> ve1 /ih [v2 ok_v2 v_uincl] ok_v1.
    exists v1 => //.
    rewrite ok_v2 /=.
    by apply (vuincl_sem_sop1 v_uincl ok_v1).
  + t_xrbindP=> ve1 /ih [v2 ok_v2 v_uincl] ok_v1.
    exists v1 => //.
    rewrite ok_v2 /=.
    by apply (vuincl_sem_sop1 v_uincl ok_v1).
  + t_xrbindP=> ve1 /ih [v2 ok_v2 v_uincl] ok_v1.
    exists v1 => //.
    rewrite ok_v2 /=.
    by apply (vuincl_sem_sop1 v_uincl ok_v1).
  + t_xrbindP=> ve1 /ih1 [v21 ok_v21 v1_uincl] ve2 /ih2 [v22 ok_v22 v2_uincl] ok_v1.
    exists v1 => //.
    rewrite ok_v21 ok_v22 /=.
    by apply (vuincl_sem_sop2 v1_uincl v2_uincl ok_v1).
  + t_xrbindP=> ve1 /ih1 [v21 ok_v21 v1_uincl] ve2 /ih2 [v22 ok_v22 v2_uincl] ok_v1.
    exists v1 => //.
    rewrite ok_v21 ok_v22 /=.
    by apply (vuincl_sem_sop2 v1_uincl v2_uincl ok_v1).
  t_xrbindP=> ve1 /ih1 [v21 ok_v21 v1_uincl] ve2 /ih2 [v22 ok_v22 v2_uincl] ok_v1.
  exists v1 => //.
  rewrite ok_v21 ok_v22 /=.
  by apply (vuincl_sem_sop2 v1_uincl v2_uincl ok_v1).
Qed.

Lemma eq_on_sem_sexpr vme vme' e :
  vme =[read_e e] vme' ->
  sem_sexpr vme e = sem_sexpr vme' e.
Proof.
  elim: e => [z|x|ws e ih|ws e ih|opk e ih|opk e1 ih1 e2 ih2|opk e1 ih1 e2 ih2|opk e1 ih1 e2 ih2] /=.
  + done.
  + apply get_var_eq_on.
    by rewrite read_e_var; clear; SvD.fsetdec.
  + by move=> /ih <-.
  + by move=> /ih <-.
  + by move=> /ih <-.
  + move=> vme_eq.
    have /ih1 <-: vme =[read_e e1] vme'.
    + apply: eq_onI vme_eq.
      rewrite {2}/read_e /= -/read_e read_eE.
      by clear; SvD.fsetdec.
    have /ih2 <-: vme =[read_e e2] vme'.
    + apply: eq_onI vme_eq.
      rewrite {2}/read_e /= -/read_e read_eE.
      by clear; SvD.fsetdec.
    done.
  + move=> vme_eq.
    have /ih1 <-: vme =[read_e e1] vme'.
    + apply: eq_onI vme_eq.
      rewrite {2}/read_e /= -/read_e read_eE.
      by clear; SvD.fsetdec.
    have /ih2 <-: vme =[read_e e2] vme'.
    + apply: eq_onI vme_eq.
      rewrite {2}/read_e /= -/read_e read_eE.
      by clear; SvD.fsetdec.
    done.
  move=> vme_eq.
  have /ih1 <-: vme =[read_e e1] vme'.
  + apply: eq_onI vme_eq.
    rewrite {2}/read_e /= -/read_e read_eE.
    by clear; SvD.fsetdec.
  have /ih2 <-: vme =[read_e e2] vme'.
  + apply: eq_onI vme_eq.
    rewrite {2}/read_e /= -/read_e read_eE.
    by clear; SvD.fsetdec.
  done.
Qed.

Lemma sem_sexpr_defined vme e v : sem_sexpr vme e = ok v -> is_defined v.
Proof.
  case: e => [z|x|ws e|ws e|opk e|opk e1 e2|opk e1 e2|opk e1 e2] /=.
  + by move=> [<-].
  + by move=> /get_varP [].
  + by rewrite /sem_sop1 /=; t_xrbindP=> _ _ ? _ <-.
  + by rewrite /sem_sop1 /=; t_xrbindP=> _ _ ? _ <-.
  + case: opk => [|ws].
    + by rewrite /sem_sop1 /=; t_xrbindP=> _ _ ? _ <-.
    by rewrite /sem_sop1 /=; t_xrbindP=> _ _ ? _ <-.
  + case: opk => [|ws].
    + by rewrite /sem_sop2 /=; t_xrbindP=> _ _ _ _ ? _ ? _ <-.
    by rewrite /sem_sop2 /=; t_xrbindP=> _ _ _ _ ? _ ? _ <-.
  + case: opk => [|ws].
    + by rewrite /sem_sop2 /=; t_xrbindP=> _ _ _ _ ? _ ? _ <-.
    by rewrite /sem_sop2 /=; t_xrbindP=> _ _ _ _ ? _ ? _ <-.
  case: opk => [|ws].
  + by rewrite /sem_sop2 /=; t_xrbindP=> _ _ _ _ ? _ ? _ <-.
  by rewrite /sem_sop2 /=; t_xrbindP=> _ _ _ _ ? _ ? _ <-.
Qed.

Lemma is_definedI v ty :
  is_defined v ->
  type_of_val v = ty ->
  match ty with
  | sbool => exists b, v = Vbool b
  | sint => exists i, v = Vint i
  | sarr len => exists a : WArray.array len, v = Varr a
  | sword ws => exists w : word ws, v = Vword w
  end.
Proof. by case: v => [b|i|len a|ws w|//] _ <- /=; eexists; reflexivity. Qed.

(* wft_DEF states that every variable in the set has a value in the current [vme]
   *AND* that this value has the same type as the variable. This second condition
   is needed to avoid problems with word variables with values smaller than their
   types, which can lead to expressions not having a semantics while well-typed.
   We show that if we are given a variable with a small value, we can extend it
   to match the type of the variable, and comply with wft_DEF.
   This is a bit of a strange lemma,
   but since, in the end, we are interested only in integers and value_uincl
   is equality on integers, we can afford to do that. *)
Lemma value_extend v ty :
  subtype (type_of_val v) ty ->
  exists2 v', value_uincl v v' & type_of_val v' = ty.
Proof.
  case: ty => [||len|ws]; [by move=> /subtypeE hty; exists v..|].
  move=> /subtypeE [ws' [hty hcmp]].
  have [->|[w ->]] := type_of_valI hty.
  + by exists (@Vword ws 0) => /=.
  exists (Vword (zero_extend ws w)) => //=.
  by apply word_uincl_zero_extR.
Qed.

Lemma wf_table_symbolic_of_pexpr e table e' table' v1 vme :
  symbolic_of_pexpr table e = ok (Some (table', e')) ->
  sem_pexpr true gd s e = ok v1 ->
  wf_table table vme s.(evm) ->
  exists vme', [/\
    wf_table table' vme' s.(evm),
    vme =[table.(vars)] vme' &
    exists2 v2,
      sem_sexpr vme' e' = ok v2 &
      value_uincl v1 v2].
Proof.
  elim: e table table' e' v1 vme => //=.
  - move=> z table _ _ _ vme [<- <-] [<-] hwft.
    exists vme; split=> //=.
    by eexists; first by reflexivity.
  - move=> x table table' e' v vme.
    case: ifP => // hlvar.
    t_xrbindP=> -[{}table' {}e'] htable [<- <-].
    move=> ok_v hwft.
    move: htable; rewrite /table_get_var.
    case hget: Mvar.get => [e|] /=.
    + move=> [<- <-].
      exists vme; split=> //.
      move: ok_v; rewrite /get_gvar hlvar.
      by apply: (hwft.(wft_sem) hget).
    rewrite /table_fresh_var.
    set x' := clone x.(gv) _.
    t_xrbindP=> /Sv_memP hnin <- <- /=.
    have [def_v /compat_type_subtype sub_v] := get_gvar_compat ok_v.
    have [v' uincl_v ty_v'] := value_extend sub_v.
    have def_v' := value_uincl_defined uincl_v def_v.
    exists vme.[x' <- v']; split=> /=.
    + case: hwft => hvars hdef hsem.
      split.
      + move=> y ey /=.
        rewrite Mvar.setP.
        case: eqP => _.
        + move=> [<-].
          rewrite read_e_var.
          by clear; SvD.fsetdec.
        move=> /hvars.
        by clear; SvD.fsetdec.
      + move=> y /= y_in.
        rewrite get_var_set;
          last by apply subtype_truncatable; rewrite clone_ty -ty_v'.
        case: eqP => [<-|hneq].
        + rewrite def_v' /= vm_truncate_val_eq clone_ty //.
          by eexists; first by reflexivity.
        apply hdef.
        by clear -hneq y_in; SvD.fsetdec.
      move=> y ey vy /=.
      rewrite Mvar.setP.
      case: eqP => [<-|_].
      + move=> [<-] /=.
        move: ok_v; rewrite /get_gvar hlvar => ok_v.
        rewrite ok_v => -[<-].
        rewrite get_var_eq clone_ty;
          last by apply subtype_truncatable; rewrite -ty_v'.
        rewrite def_v' /= vm_truncate_val_eq //.
        by eexists; first by reflexivity.
      move=> hey ok_vy.
      have [vy' ok_vy' incl_vy] := hsem _ _ _ hey ok_vy.
      exists vy' => //.
      rewrite -ok_vy'.
      apply eq_on_sem_sexpr.
      move=> y' y'_in.
      rewrite Vm.setP_neq //.
      apply /eqP => /=.
      have := hvars _ _ hey.
      by clear -y'_in hnin; SvD.fsetdec.
    + move=> y yin.
      rewrite Vm.setP_neq //.
      apply /eqP.
      by clear -hnin yin; congruence.
    exists v' => //.
    rewrite get_var_eq clone_ty;
      last by apply subtype_truncatable; rewrite -ty_v'.
    by rewrite def_v' /= vm_truncate_val_eq.
  - move=> op e he table table' e' v vme.
    apply: robindP => op' ok_op'.
    t_xrbindP=> ote hsym.
    apply: robindP=> -[{}table' {}e'] ? [<- <-]; subst ote.
    move=> ve ok_ve ok_v hwft.
    have [vme1 [hwft1 hincl1 hseme1]] := he _ _ _ _ _ hsym ok_ve hwft.
    exists vme1; split=> //=.
    have [v' ok_v' incl_v] := hseme1.
    case: op ok_op' ok_v => //.
    + move=> ws [<-] /=.
      rewrite ok_v' /=.
      move=> /(vuincl_sem_sop1 incl_v) ->.
      by eexists; first by reflexivity.
    + move=> ws [<-] /=.
      rewrite ok_v' /=.
      move=> /(vuincl_sem_sop1 incl_v) ->.
      by eexists; first by reflexivity.
    move=> opk [<-] /=.
    rewrite ok_v' /=.
    move=> /(vuincl_sem_sop1 incl_v) ->.
    by eexists; first by reflexivity.
  move=> op e1 he1 e2 he2 table table' e' v vme.
  apply: robindP => op' ok_op'.
  t_xrbindP=> ote1 hsym1.
  apply: robindP=> -[table1 e1'] ?; subst ote1.
  t_xrbindP=> ote2 hsym2.
  apply: robindP=> -[table2 e2'] ?; subst ote2.
  move=> [<- <-].
  move=> ve1 ok_ve1 ve2 ok_ve2 ok_v hwft.
  have [vme1 [hwft1 hincl1 hseme1]] := he1 _ _ _ _ _ hsym1 ok_ve1 hwft.
  have [vme2 [hwft2 hincl2 hseme2]] := he2 _ _ _ _ _ hsym2 ok_ve2 hwft1.
  exists vme2; split=> //=.
  + apply: (eq_onT hincl1).
    apply: eq_onI hincl2.
    by apply (symbolic_of_pexpr_subset_vars hsym1 hwft.(wft_vars)).
  have [v' ok_v' incl_v] := hseme1.
  have [v2' ok_v2' incl_v2] := hseme2.
  case: op ok_op' ok_v => //.
  + move=> opk [<-] /=.
    have ok_v'': sem_sexpr vme2 e1' = ok v'.
    + have heq: vme1 =[read_e e1'] vme2.
      + apply: eq_onI hincl2.
        by apply (symbolic_of_pexpr_subset_read hsym1 hwft.(wft_vars)).
      by rewrite -(eq_on_sem_sexpr heq).
    rewrite ok_v'' ok_v2' /=.
    move=> /(vuincl_sem_sop2 incl_v incl_v2) ->.
    by eexists; first by reflexivity.
  + move=> opk [<-] /=.
    have ok_v'': sem_sexpr vme2 e1' = ok v'.
    + have heq: vme1 =[read_e e1'] vme2.
      + apply: eq_onI hincl2.
        by apply (symbolic_of_pexpr_subset_read hsym1 hwft.(wft_vars)).
      by rewrite -(eq_on_sem_sexpr heq).
    rewrite ok_v'' ok_v2' /=.
    move=> /(vuincl_sem_sop2 incl_v incl_v2) ->.
    by eexists; first by reflexivity.
  move=> opk [<-] /=.
  have ok_v'': sem_sexpr vme2 e1' = ok v'.
  + have heq: vme1 =[read_e e1'] vme2.
    + apply: eq_onI hincl2.
      by apply (symbolic_of_pexpr_subset_read hsym1 hwft.(wft_vars)).
    by rewrite -(eq_on_sem_sexpr heq).
  rewrite ok_v'' ok_v2' /=.
  move=> /(vuincl_sem_sop2 incl_v incl_v2) ->.
  by eexists; first by reflexivity.
Qed.

End WF_TABLE_SYMBOLIC_OF_PEXPR.

End CLONE.

Lemma eq_on_sem_slice vme vme' s :
  vme =[read_slice s] vme' ->
  sem_slice vme s = sem_slice vme' s.
Proof.
  move=> vme_eq.
  rewrite /sem_slice.
  rewrite !(eq_on_sem_sexpr (vme':=vme')) //.
  + apply: eq_onI vme_eq.
    rewrite /read_slice.
    by clear; SvD.fsetdec.
  apply: eq_onI vme_eq.
  rewrite /read_slice.
  by clear; SvD.fsetdec.
Qed.

Lemma eq_on_sem_zone_aux vme vme' cs z :
  vme =[read_zone z] vme' ->
  sem_zone_aux vme cs z = sem_zone_aux vme' cs z.
Proof.
  elim: z cs => [//|s z ih] /= cs vme_eq.
  rewrite (eq_on_sem_slice (vme':=vme'));
    last by apply: eq_onI vme_eq; clear; SvD.fsetdec.
  case: sem_slice => //= ?.
  case: sub_concrete_slice => //= ?.
  apply ih.
  by apply: eq_onI vme_eq; clear; SvD.fsetdec.
Qed.

Lemma eq_on_sem_zone vme vme' z :
  vme =[read_zone z] vme' ->
  sem_zone vme z = sem_zone vme' z.
Proof.
  case: z => [//|s z] /= vme_eq.
  rewrite (eq_on_sem_slice (vme':=vme'));
    last by apply: eq_onI vme_eq; clear; SvD.fsetdec.
  case: sem_slice => //= ?.
  apply eq_on_sem_zone_aux.
  by apply: eq_onI vme_eq; clear; SvD.fsetdec.
Qed.

Lemma eq_on_sub_region_addr vme vme' sr :
  vme =[read_zone sr.(sr_zone)] vme' ->
  sub_region_addr vme sr = sub_region_addr vme' sr.
Proof.
  move=> vme_eq.
  rewrite /sub_region_addr.
  by rewrite (eq_on_sem_zone vme_eq).
Qed.

Lemma eq_on_sem_interval vme vme' i :
  vme =[read_interval i] vme' ->
  mapM (sem_slice vme) i = mapM (sem_slice vme') i.
Proof.
  elim: i => [//|s i ih] /= vme_eq.
  rewrite (eq_on_sem_slice (vme':=vme'));
    last by apply: eq_onI vme_eq; clear; SvD.fsetdec.
  case: sem_slice => //= ?.
  rewrite ih //.
  by apply: eq_onI vme_eq; clear; SvD.fsetdec.
Qed.

Lemma eq_on_valid_offset_interval vme vme' i off :
  vme =[read_interval i] vme' ->
  valid_offset_interval vme i off <-> valid_offset_interval vme' i off.
Proof.
  move=> vme_eq.
  by split=> off_valid ci ok_ci; apply off_valid; rewrite -ok_ci; [|symmetry];
    apply (eq_on_sem_interval vme_eq).
Qed.

Lemma valid_offset_eq_on vars vme vme' status off :
  vme =[vars] vme' ->
  wf_vars_status vars status ->
  valid_offset vme status off <-> valid_offset vme' status off.
Proof.
  move=> vme_eq.
  case: status => //= i hvars.
  apply eq_on_valid_offset_interval.
  by apply (eq_onI hvars vme_eq).
Qed.

Lemma wf_sub_region_eq_on vars vme vme' sr vm :
  vme =[vars] vme' ->
  wf_vars_zone vars sr.(sr_zone) ->
  wf_sub_region vme sr vm ->
  wf_sub_region vme' sr vm.
Proof.
  move=> vme_eq hvars.
  case=> hwfr [cs ok_cs wf_cs].
  split=> //.
  exists cs => //.
  rewrite -ok_cs; symmetry.
  apply eq_on_sem_zone.
  by apply (eq_onI hvars vme_eq).
Qed.

Lemma wf_status_eq_on vars vme vme' status :
  vme =[vars] vme' ->
  wf_vars_status vars status ->
  wf_status vme status ->
  wf_status vme' status.
Proof.
  move=> vme_eq.
  case: status => //= i hvars [ci ok_ci].
  exists ci.
  rewrite -ok_ci; symmetry.
  apply eq_on_sem_interval.
  by apply (eq_onI hvars vme_eq).
Qed.

Lemma eq_sub_region_val_eq_on vars vme vme' ty m sr status v :
  vme =[vars] vme' ->
  wf_vars_zone vars sr.(sr_zone) ->
  wf_vars_status vars status ->
  eq_sub_region_val ty vme m sr status v ->
  eq_sub_region_val ty vme' m sr status v.
Proof.
  move=> vme_eq hvarsz hvarss [hread hty].
  split=> // off addr w haddr off_valid ok_w.
  apply: hread ok_w.
  + by rewrite (eq_on_sub_region_addr (eq_onI hvarsz vme_eq)).
  by apply (valid_offset_eq_on off vme_eq hvarss).
Qed.

Lemma check_gvalid_wf_vars_zone vars rmap x sr status :
  wfr_VARS_ZONE vars rmap ->
  check_gvalid rmap x = Some (sr, status) ->
  wf_vars_zone vars sr.(sr_zone).
Proof.
  move=> hvars.
  rewrite /check_gvalid.
  case: ifP => _.
  + case: Mvar.get => [[_ ws]|] //= [<- _] /=.
    rewrite /wf_vars_zone /= /read_slice /= /read_e /=.
    by clear; SvD.fsetdec.
  case hsr: Mvar.get => [{}sr|//] [<- _].
  by apply: hvars hsr.
Qed.

Lemma check_gvalid_wf_vars_status vars (rmap:region_map) x sr status :
  wfr_VARS_STATUS vars rmap ->
  check_gvalid rmap x = Some (sr, status) ->
  wf_vars_status vars status.
Proof.
  move=> hvars.
  rewrite /check_gvalid.
  case: ifP => _.
  + by case: Mvar.get => [[_ _]|] //= [_ <-] /=.
  case: Mvar.get => [{}sr|//] [_ <-].
  by apply hvars.
Qed.

Lemma wf_rmap_eq_on vars rmap vme vme' s1 s2 :
  vme =[vars] vme' ->
  wf_rmap vars rmap vme s1 s2 ->
  wf_rmap vars rmap vme' s1 s2.
Proof.
  move=> vme_eq.
  case=> hwfsr hwfst hvarsz hvarss hval hptr.
  split=> //.
  + move=> x sr /[dup] /hvarsz hvars /hwfsr hwf.
    by apply (wf_sub_region_eq_on vme_eq hvars hwf).
  + move=> r x.
    by apply (wf_status_eq_on vme_eq (hvarss _ _)).
  + move=> x sr status v hgvalid hgget.
    have {hgget} heqval := hval _ _ _ _ hgvalid hgget.
    have sr_vars := check_gvalid_wf_vars_zone hvarsz hgvalid.
    have status_vars := check_gvalid_wf_vars_status hvarss hgvalid.
    by apply (eq_sub_region_val_eq_on vme_eq).
  move=> x sr /[dup] hsr /hptr [pk [hget hpk]].
  exists pk; split=> //.
  case: pk hpk {hget} => //=.
  + move=> xp hxp ofs haddr; apply hxp.
    by rewrite (eq_on_sub_region_addr (eq_onI (hvarsz _ _ hsr) vme_eq)).
  move=> s ofs ws cs f hpk hcheck pofs ofs' ok_pofs ok_ofs'.
  apply hpk => //.
  by rewrite (eq_on_sub_region_addr (eq_onI (hvarsz _ _ hsr) vme_eq)).
Qed.

Lemma subset_vars_wf_vars_zone vars1 vars2 z :
  Sv.Subset vars1 vars2 ->
  wf_vars_zone vars1 z ->
  wf_vars_zone vars2 z.
Proof.
  rewrite /wf_vars_zone.
  by clear; SvD.fsetdec.
Qed.

Lemma subset_vars_wf_vars_status vars1 vars2 status :
  Sv.Subset vars1 vars2 ->
  wf_vars_status vars1 status ->
  wf_vars_status vars2 status.
Proof.
  move=> hsubset.
  case: status => //= i.
  rewrite /wf_vars_interval.
  by clear -hsubset; SvD.fsetdec.
Qed.

Lemma subset_vars_wf_rmap vars1 vars2 rmap vme s1 s2 :
  Sv.Subset vars1 vars2 ->
  wf_rmap vars1 rmap vme s1 s2 ->
  wf_rmap vars2 rmap vme s1 s2.
Proof.
  move=> hsubset.
  case=> hwfsr hwfst hvarsz hvarss hval hptr.
  split=> //.
  + move=> x sr /hvarsz.
    by apply (subset_vars_wf_vars_zone hsubset).
  move=> r x.
  by apply (subset_vars_wf_vars_status hsubset).
Qed.

Lemma valid_state_eq_on vme vme' table table' rmap m0 s1 s2 :
  vme =[table.(vars)] vme' ->
  Sv.Subset table.(vars) table'.(vars) ->
  wf_table table' vme' s1.(evm) ->
  valid_state table rmap vme m0 s1 s2 ->
  valid_state table' rmap vme' m0 s1 s2.
Proof.
  move=> vme_eq hsubset hwft'.
  case=>
    /= hscs hvalid hdisj hincl hincl2 hunch hrip hrsp heqvm hwft hwfr heqmem
    hglobv htop.
  split=> //.
  apply (subset_vars_wf_rmap hsubset).
  by apply: wf_rmap_eq_on.
Qed.

Lemma wf_table_set_var table vme vm x v :
  wf_table table vme vm ->
  wf_table (remove_binding table x) vme vm.[x <- v].
Proof.
  case=> hvars hdef hsem.
  constructor=> //.
  + move=> y ey /=.
    rewrite Mvar.removeP.
    case: eq_op => //.
    by apply hvars.
  move=> y ey vy /=.
  rewrite Mvar.removeP.
  case: eqP => // hneq.
  rewrite get_var_neq //.
  by apply hsem.
Qed.

Lemma wf_table_set_lval wdb gd r v s1 s2 table se :
  write_lval wdb gd r v s1 = ok s2 ->
  wf_table table se s1.(evm) ->
  wf_table (remove_binding_lval table r) se s2.(evm).
Proof.
  case: r => /=.
  + by move=> _ _ /write_noneP [-> _ _].
  + move=> x /write_varP [-> _ _] /=.
    by apply wf_table_set_var.
  + move=> ????.
    by t_xrbindP=> ???????????? <- /=.
  + move=> ?????.
    apply: on_arr_varP => ????.
    t_xrbindP=> ???????? /write_varP [-> _ _] /=.
    by apply wf_table_set_var.
  move=> ?????.
  apply: on_arr_varP => ????.
  t_xrbindP=> ???????? /write_varP [-> _ _] /=.
  by apply wf_table_set_var.
Qed.

Lemma valid_state_set_var table rmap vme m0 s1 s2 x v :
  valid_state table rmap vme m0 s1 s2 ->
  get_local pmap x = None ->
  ¬ Sv.In x (vnew pmap) ->
  valid_state (remove_binding table x) rmap vme m0
    (with_vm s1 (evm s1).[x <- v]) (with_vm s2 (evm s2).[x <- v]).
Proof.
  case: s1 s2 => scs1 mem1 vm1 [scs2 mem2 vm2].
  case=>
    /= hscs hvalid hdisj hincl hincl2 hunch hrip hrsp heqvm hwft hwfr heqmem
    hglobv htop hget hnin.
  constructor => //=.
  + by rewrite Vm.setP_neq //; assert (h:=rip_in_new); apply/eqP => ?; subst x; apply hnin.
  + by rewrite Vm.setP_neq //; assert (h:=rsp_in_new); apply/eqP => ?; subst x; apply hnin.
  + by move=> y hy hnnew; rewrite !Vm.setP heqvm.
  + by apply: wf_table_set_var hwft.
  rewrite /with_vm /=; case: hwfr => hwfsr hwfst hvarsz hvarss hval hptr.
  constructor => //.
  + move=> y sr bytes vy hy; have ? := get_localn_checkg_diff hget hptr hy.
    by rewrite get_gvar_neq //; apply hval.
  move=> y mp hy; have [pk [hgety hpk]]:= hptr y mp hy; exists pk; split => //.
  case: pk hgety hpk => //= yp hyp.
  assert (h := wfr_new (wf_locals hyp)).
  by rewrite Vm.setP_neq //;apply /eqP => /=; clear -h hnin; SvD.fsetdec.
Qed.

Lemma eq_sub_region_val_disjoint_zrange_ovf p sz mem1 mem2 vme sr w ty status v :
  (forall al p1 ws1,
      disjoint_zrange_ovf p sz p1 (wsize_size ws1) ->
      read mem2 al p1 ws1 = read mem1 al p1 ws1) ->
  sub_region_addr vme sr = ok w ->
  disjoint_zrange_ovf p sz w (size_of ty) ->
  eq_sub_region_val ty vme mem1 sr status v ->
  eq_sub_region_val ty vme mem2 sr status v.
Proof.
  move=> hreadeq ok_w hd [hread hty]; split=> // off ofs w' ok_ofs hoff hget.
  move: ok_w; rewrite ok_ofs => -[?]; subst w.
  rewrite -(hread _ _ _ ok_ofs hoff hget).
  apply hreadeq => i i' hi.
  rewrite /wsize_size /= => hi'.
  have {} hi' : i' = 0 by lia.
  subst.
  rewrite add_0 -addE.
  apply: hd => //.
  exact: get_val_byte_bound hget.
Qed.

Lemma disjoint_source_word table rmap vme m0 s1 s2 :
  valid_state table rmap vme m0 s1 s2 ->
  forall s al p ws,
    Sv.In s Slots -> validw s1.(emem) al p ws ->
    disjoint_zrange_ovf p (wsize_size ws) (Addr s) (size_slot s).
Proof.
  move=> hvs s al p ws hin /validwP [] hal hd i i' /hd.
  rewrite (validw8_alignment Aligned) !addE => hi hi'.
  case: (vs_disjoint hin hi).
  rewrite /wsize_size /= => /ZleP hs _ D K.
  move: D.
  have -> : wunsigned (p + wrepr _ i) = wunsigned (Addr s + wrepr _ i') by rewrite K.
  have ? := wunsigned_range (Addr s).
  rewrite wunsigned_add; lia.
Qed.

Lemma eq_sub_region_val_disjoint_zrange p sz mem1 mem2 vme sr w ty status v :
  (forall al p1 ws1,
    disjoint_zrange p sz p1 (wsize_size ws1) ->
    read mem2 al p1 ws1 = read mem1 al p1 ws1) ->
  sub_region_addr vme sr = ok w ->
  disjoint_zrange p sz w (size_of ty) ->
  eq_sub_region_val ty vme mem1 sr status v ->
  eq_sub_region_val ty vme mem2 sr status v.
Proof.
  move=> hreadeq ok_w hd [hread hty]; split=> // off ofs w' ok_ofs hoff hget.
  move: ok_w; rewrite ok_ofs => -[?]; subst w.
  rewrite -(hread _ _ _ ok_ofs hoff hget).
  apply hreadeq.
  apply (disjoint_zrange_byte hd).
  rewrite -hty.
  by apply (get_val_byte_bound hget).
Qed.

Lemma wf_region_slot_inj r1 r2 :
  wf_region r1 -> wf_region r2 ->
  r1.(r_slot) = r2.(r_slot) ->
  r1 = r2.
Proof.
  move=> hwf1 hwf2.
  have := hwf1.(wfr_align).
  have := hwf2.(wfr_align).
  have := hwf1.(wfr_writable).
  have := hwf2.(wfr_writable).
  by case: (r1); case: (r2) => /=; congruence.
Qed.

Lemma distinct_regions_disjoint_zrange vme sr1 sr2 ty1 ty2 ofs1 ofs2 :
  wf_sub_region vme sr1 ty1 ->
  sub_region_addr vme sr1 = ok ofs1 ->
  wf_sub_region vme sr2 ty2 ->
  sub_region_addr vme sr2 = ok ofs2 ->
  sr1.(sr_region) <> sr2.(sr_region) ->
  sr1.(sr_region).(r_writable) ->
  disjoint_zrange ofs1 (size_of ty1) ofs2 (size_of ty2).
Proof.
  move=> hwf1 haddr1 hwf2 haddr2 hneq hw.
  have hb1 := zbetween_sub_region_addr hwf1 haddr1.
  have hb2 := zbetween_sub_region_addr hwf2 haddr2.
  apply (disjoint_zrange_incl hb1 hb2).
  apply (disjoint_writable hwf1.(wfr_slot) hwf2.(wfr_slot));
    last by rewrite hwf1.(wfr_writable).
  by move=> /(wf_region_slot_inj hwf1 hwf2).
Qed.

Lemma eq_sub_region_val_distinct_regions vme sr ty ofs sry ty' s2 mem2 status v :
  wf_sub_region vme sr ty ->
  sub_region_addr vme sr = ok ofs ->
  wf_sub_region vme sry ty' ->
  sr.(sr_region) <> sry.(sr_region) ->
  sr.(sr_region).(r_writable) ->
  (forall al p ws,
    disjoint_zrange ofs (size_of ty) p (wsize_size ws) ->
    read mem2 al p ws = read (emem s2) al p ws) ->
  eq_sub_region_val ty' vme (emem s2) sry status v ->
  eq_sub_region_val ty' vme mem2 sry status v.
Proof.
  move=> hwf haddr hwfy hneq hw hreadeq.
  have [ofsy haddry] := wf_sub_region_sub_region_addr hwfy.
  apply (eq_sub_region_val_disjoint_zrange hreadeq haddry).
  by apply (distinct_regions_disjoint_zrange hwf haddr hwfy haddry).
Qed.

Lemma disjoint_zones_sym z1 z2 : disjoint_zones z1 z2 = disjoint_zones z2 z1.
Proof.
  elim: z1 z2 => [|s1 z1 ih] [|s2 z2] //=.
  rewrite eq_sym.
  case: eqP => _ //.
  case: symbolic_slice_ble => // b1.
  case: symbolic_slice_ble => // b2.
  by case: b1 b2 => [] [].
Qed.

Lemma incl_interval_refl : Reflexive incl_interval.
Proof. by move=> i; apply /allP. Qed.

Lemma incl_interval_trans : Transitive incl_interval.
Proof.
  move=> i1 i2 i3 /allP hincl1 /allP hincl2.
  by apply /allP => i /hincl1 /hincl2.
Qed.

Lemma incl_interval_cons s i :
  incl_interval i (s :: i).
Proof.
  rewrite /incl_interval.
  apply /allP => s1 s1_in.
  rewrite in_cons.
  by apply /orP; right.
Qed.

Lemma add_sub_interval_incl_l i1 s i2 :
  add_sub_interval i1 s = Some i2 ->
  incl_interval i1 i2.
Proof.
  elim: i1 i2 => [//|s1 i1 ih1] i2 /=.
  case: eqP => [<-|_].
  + move=> [<-] /=.
    rewrite mem_head /=.
    by apply incl_interval_cons.
  case: (odflt _ _).
  + move=> [<-] /=.
    rewrite in_cons mem_head orbT /=.
    apply: incl_interval_trans (incl_interval_cons _ _).
    by apply incl_interval_cons.
  case: (odflt _ _) => //.
  apply: obindP => {}i2 hadd [<-].
  rewrite mem_head /=.
  apply (incl_interval_trans (ih1 _ hadd)).
  by apply incl_interval_cons.
Qed.

Lemma add_sub_interval_incl_r i1 s i2 :
  add_sub_interval i1 s = Some i2 ->
  incl_interval [::s] i2.
Proof.
  elim: i1 i2 => [|s1 i1 ih1] i2 /=.
  + move=> [<-] /=.
    by rewrite mem_head.
  case: eqP => [<-|_].
  + move=> [<-] /=.
    by rewrite mem_head.
  case: (odflt _ _).
  + move=> [<-] /=.
    by rewrite mem_head.
  case: (odflt _ _) => //.
  apply: obindP => {}i2 hadd [<-] /=.
  rewrite in_cons.
  have /= /andP [-> _] := ih1 _ hadd.
  by rewrite orbT.
Qed.

Lemma incl_interval_wf_interval i1 i2 vme :
  incl_interval i1 i2 ->
  wf_interval vme i2 ->
  wf_interval vme i1.
Proof.
  elim: i1 i2 => [|s1 i1 ih1] i2 /=.
  + move=> _ _.
    by exists [::].
  move=> /andP [/InP s1_in /ih1{}ih1] /[dup] {}/ih1 [ci1 ok_ci1] [ci2 ok_ci2].
  have [cs1 [_ ok_cs1]] := mapM_In ok_ci2 s1_in.
  exists (cs1::ci1).
  by rewrite /= ok_cs1 ok_ci1 /=.
Qed.

Lemma wf_interval_add_sub_interval i1 s i2 vme cs :
  add_sub_interval i1 s = Some i2 ->
  wf_interval vme i1 ->
  sem_slice vme s = ok cs ->
  wf_interval vme i2.
Proof.
  move=> hadd [ci1 ok_ci1] ok_cs.
  elim: i1 i2 hadd ci1 ok_ci1 => [|s1 i1 ih1] i2 /=.
  + move=> [<-] _ _.
    exists [::cs].
    by rewrite /= ok_cs /=.
  case: eqP => _.
  + move=> [<-] ci1 ok_ci1.
    by exists ci1.
  case: (odflt _ _).
  + move=> [<-].
    t_xrbindP=> _ cs1 ok_cs1 ci1 ok_ci1 _.
    exists (cs :: cs1 :: ci1).
    by rewrite /= ok_cs ok_cs1 ok_ci1 /=.
  case: (odflt _ _) => //.
  apply: obindP => {}i2 hadd [<-].
  t_xrbindP=> _ cs1 ok_cs1 ci1 ok_ci1 _.
  have [ci2 ok_ci2] := ih1 _ hadd _ ok_ci1.
  exists (cs1 :: ci2).
  by rewrite /= ok_cs1 ok_ci2 /=.
Qed.

Lemma add_sub_interval_vars i1 s i2 :
  add_sub_interval i1 s = Some i2 ->
  Sv.Subset (read_interval i2) (Sv.union (read_interval i1) (read_slice s)).
Proof.
  elim: i1 i2 => [|s1 i1 ih1] i2 /=.
  + move=> [<-] /=.
    by clear; SvD.fsetdec.
  case: eqP => _.
  + move=> [<-] /=.
    by clear; SvD.fsetdec.
  case: ifP => _.
  + move=> [<-] /=.
    by clear; SvD.fsetdec.
  case: ifP => _ //.
  apply: obindP=> {}i2 hadd [<-] /=.
  have := ih1 _ hadd.
  by clear; SvD.fsetdec.
Qed.

Lemma incl_intervalP i1 i2 vme off :
  incl_interval i1 i2 ->
  wf_interval vme i2 ->
  valid_offset_interval vme i2 off ->
  valid_offset_interval vme i1 off.
Proof.
  move=> hincl [ci2 ok_ci2] /(_ ci2 ok_ci2) off_valid2 ci1 ok_ci1 off_valid1.
  move: off_valid1 => /(has_nthP {| cs_ofs := 0; cs_len := 0 |}) [k1 hk1' off_in1].
  have := hk1'; rewrite -(size_mapM ok_ci1) => hk1.
  move: hincl => /(all_nthP {| ss_ofs := Sconst 0; ss_len := Sconst 0 |}) /(_ k1 hk1).
  move=> /(nthP {| ss_ofs := Sconst 0; ss_len := Sconst 0 |}) [k2 hk2 heqsub].
  have := hk2; rewrite (size_mapM ok_ci2) => hk2'.
  apply /off_valid2 /(has_nthP {| cs_ofs := 0; cs_len := 0 |}).
  exists k2 => //.
  have := mapM_nth {| ss_ofs := Sconst 0; ss_len := Sconst 0 |} {| cs_ofs := 0; cs_len := 0 |} ok_ci1 hk1.
  have := mapM_nth {| ss_ofs := Sconst 0; ss_len := Sconst 0 |} {| cs_ofs := 0; cs_len := 0 |} ok_ci2 hk2.
  by rewrite heqsub => -> [->].
Qed.

Lemma valid_offset_interval_add_sub_interval i1 s i2 vme cs off :
  add_sub_interval i1 s = Some i2 ->
  wf_interval vme i1 ->
  sem_slice vme s = ok cs ->
  valid_offset_interval vme i2 off ->
  valid_offset_interval vme i1 off /\ ~ offset_in_concrete_slice cs off.
Proof.
  move=> hadd i1_wf ok_cs off_valid.
  have i2_wf := wf_interval_add_sub_interval hadd i1_wf ok_cs.
  split.
  + by apply (incl_intervalP (add_sub_interval_incl_l hadd) i2_wf off_valid).
  have := incl_intervalP (add_sub_interval_incl_r hadd) i2_wf off_valid.
  rewrite /valid_offset_interval /= ok_cs /= => /(_ _ erefl) /=.
  by rewrite orbF.
Qed.

Lemma wf_status_clear_status vme status z cs :
  wf_status vme status ->
  sem_zone vme z = ok cs ->
  wf_status vme (odflt Unknown (clear_status status z)).
Proof.
  move=> hwfs ok_cs.
  case: z ok_cs => [//|s z] ok_cs /=.
  have [cs' ok_cs' _] := sem_zone_cons_incl ok_cs.
  case: status hwfs => //=.
  + move=> _.
    rewrite /wf_interval /= ok_cs' /=.
    by eexists; reflexivity.
  move=> i1 i1_wf.
  case hadd: add_sub_interval => [i2|//] /=.
  by apply (wf_interval_add_sub_interval hadd i1_wf ok_cs').
Qed.

Lemma wf_vars_status_clear_status vars status z :
  wf_vars_status vars status ->
  wf_vars_zone vars z ->
  wf_vars_status vars (odflt Unknown (clear_status status z)).
Proof.
  case: z => [//|s z] /=.
  case: status => //=.
  + move=> _.
    rewrite /wf_vars_zone /wf_vars_interval /=.
    by clear; SvD.fsetdec.
  move=> i1.
  case hadd: add_sub_interval => [i2|//] /=.
  have := add_sub_interval_vars hadd.
  rewrite /wf_vars_interval /wf_vars_zone /=.
  by clear; SvD.fsetdec.
Qed.

Lemma valid_offset_clear_status vme status z cs off :
  wf_status vme status ->
  sem_zone vme z = ok cs ->
  valid_offset vme (odflt Unknown (clear_status status z)) off ->
  valid_offset vme status off /\ ~ offset_in_concrete_slice cs off.
Proof.
  case: z => [//|s _] hwfs /sem_zone_cons_incl /= [cs' ok_cs' hsub] off_valid.
  suff: valid_offset vme status off /\ ~ offset_in_concrete_slice cs' off.
  + move=> [{}off_valid off_nin].
    split=> // off_in; apply off_nin.
    by apply (zbetween_concrete_sliceP hsub off_in).
  case: status hwfs off_valid => //=.
  + move=> _ off_valid; split=> // off_in.
    apply (off_valid [:: cs']).
    + by rewrite /= ok_cs' /=.
    by rewrite /= orbF.
  move=> i1 i1_wf.
  case hadd: add_sub_interval => [i2|//] /=.
  by apply (valid_offset_interval_add_sub_interval hadd i1_wf ok_cs').
Qed.

Definition disjoint_symbolic_slice vme s1 s2 :=
  forall cs1 cs2,
  sem_slice vme s1 = ok cs1 ->
  sem_slice vme s2 = ok cs2 ->
  disjoint_concrete_slice cs1 cs2.

Definition disjoint_symbolic_zone vme z1 z2 :=
  forall cs1 cs2,
  sem_zone vme z1 = ok cs1 ->
  sem_zone vme z2 = ok cs2 ->
  disjoint_concrete_slice cs1 cs2.

Lemma disjoint_symbolic_slice_sym vme s1 s2 :
  disjoint_symbolic_slice vme s1 s2 ->
  disjoint_symbolic_slice vme s2 s1.
Proof.
  move=> hdisj cs1 cs2 ok_cs1 ok_cs2.
  rewrite disjoint_concrete_slice_sym.
  by apply hdisj.
Qed.

Lemma disjoint_symbolic_zone_cons vme s z1 z2 :
  z1 <> [::] -> z2 <> [::] ->
  disjoint_symbolic_zone vme z1 z2 ->
  disjoint_symbolic_zone vme (s::z1) (s::z2).
Proof.
  case: z1 => // s1 z1 _.
  case: z2 => // s2 z2 _.
  move=> hdisj cs1 cs2 /=.
  t_xrbindP=> cs -> /= cs1' ok_cs1' cs1'' ok_cs1'' ok_cs1
    _ [<-] cs2' ok_cs2' cs2'' ok_cs2'' ok_cs2.
  have [{}cs1'' {}ok_cs1'' {}ok_cs1] :=
    sem_zone_aux_sub_concrete_slice ok_cs1 ok_cs1''.
  have [{}cs2'' {}ok_cs2'' {}ok_cs2] :=
    sem_zone_aux_sub_concrete_slice ok_cs2 ok_cs2''.
  apply (sub_concrete_slice_disjoint ok_cs1 ok_cs2).
  apply hdisj.
  + by rewrite /= ok_cs1' /= ok_cs1'' /=.
  by rewrite /= ok_cs2' /= ok_cs2'' /=.
Qed.

(* under-specification *)
(* TODO: remove disjoint_symbolic_slice and reason on concrete_slice only *)
Lemma symbolic_slice_ble_disjoint vme s1 s2 :
  odflt false (symbolic_slice_ble s1 s2) ->
  disjoint_symbolic_slice vme s1 s2.
Proof.
  move=> + cs1 cs2.
  rewrite /symbolic_slice_ble /sem_slice.
  case: is_constP => //= ofs1.
  case: is_constP => //= len1.
  case: is_constP => //= ofs2.
  move=> hle [<-].
  t_xrbindP=> len2 vlen2 ok_vlen2 ok_len2 <-.
  by rewrite /disjoint_concrete_slice /= hle.
Qed.

Lemma disjoint_symbolic_slice_zone vme s1 s2 z1 z2 :
  disjoint_symbolic_slice vme s1 s2 ->
  disjoint_symbolic_zone vme (s1 :: z1) (s2 :: z2).
Proof.
  move=> hdisj cs1 cs2.
  move=> /sem_zone_cons_incl [cs1' ok_cs1' hb1].
  move=> /sem_zone_cons_incl [cs2' ok_cs2' hb2].
  apply (disjoint_concrete_slice_incl hb1 hb2).
  by apply hdisj.
Qed.

(* La fonction [disjoint_zones] n'a pas de cas particulier pour les constantes ?
   pourrait-on réécrire en fonction de get_suffix ? *)
Lemma get_suffix_Some_None vme z1 z2 :
  get_suffix z1 z2 = Some None ->
  disjoint_symbolic_zone vme z1 z2.
Proof.
  elim: z1 z2 => [//|s1 z1 ih1] [//|s2 z2] /=.
  case: eqP => [<-|_].
  + move=> hsuffix.
    apply disjoint_symbolic_zone_cons.
    + by case: (z1) hsuffix.
    + by case: (z1) (z2) hsuffix => [//|??] [].
    by apply ih1.
  move=> hsuffix; apply disjoint_symbolic_slice_zone; move: hsuffix.
  case hle1: (odflt _ _).
  + move=> _.
    by apply symbolic_slice_ble_disjoint.
  case hle2: (odflt _ _).
  + move=> _.
    apply disjoint_symbolic_slice_sym.
    by apply symbolic_slice_ble_disjoint.
  case: z1 {ih1} => //.
  case: is_const => // ?.
  case: is_const => // ?.
  case: is_const => // ?.
  case: is_const => // ?.
  by case: ifP.
Qed.

Lemma sub_concrete_slice_offset cs1 cs2 cs :
  sub_concrete_slice cs1 cs2 = ok cs ->
  forall off,
    offset_in_concrete_slice cs off =
    offset_in_concrete_slice cs2 (off - cs1.(cs_ofs)).
Proof.
  rewrite /sub_concrete_slice.
  case: ifP => // _ [<-].
  move=> off.
  rewrite /offset_in_concrete_slice /=.
  by apply /idP/idP; rewrite !zify; lia.
Qed.

Lemma get_suffix_Some_Some vme z1 z2 z cs1 cs2 :
  z <> [::] ->
  get_suffix z1 z2 = Some (Some z) ->
  sem_zone vme z1 = ok cs1 ->
  sem_zone vme z2 = ok cs2 ->
  exists2 cs,
    sem_zone vme z = ok cs &
      forall off,
        offset_in_concrete_slice cs1 off ->
        offset_in_concrete_slice cs2 off ->
        offset_in_concrete_slice cs (off - cs1.(cs_ofs)).
Proof.
  move=> z_nnil.
  elim: z1 z2 cs1 cs2 => [//|s1 z1 ih1] [//|s2 z2] cs1 cs2 //=.
  case: eqP => [<-|_].
  + t_xrbindP=> hsuffix cs1' -> /= ok_cs1 _ [<-] ok_cs2.
    have: z1 = [::] \/ z1 <> [::].
    + by case: (z1); [left|right].
    case=> [?|z1_nnil].
    + subst z1.
      move: hsuffix ok_cs1 => /= [?] [?]; subst z2 cs1'.
      have [cs ok_cs {}ok_cs2] := sem_zone_aux_sem_zone z_nnil ok_cs2.
      exists cs => //.
      move=> off hoff1 hoff2.
      by rewrite -(sub_concrete_slice_offset ok_cs2).
    have: z2 = [::] \/ z2 <> [::].
    + by case: (z2); [left|right].
    case=> [?|z2_nnil].
    + subst z2.
      by case: (z1) z1_nnil hsuffix.
    have [cs1'' ok_cs1'' {}ok_cs1] := sem_zone_aux_sem_zone z1_nnil ok_cs1.
    have [cs2'' ok_cs2'' {}ok_cs2] := sem_zone_aux_sem_zone z2_nnil ok_cs2.
    have [cs ok_cs hoff] := ih1 _ _ _ hsuffix ok_cs1'' ok_cs2''.
    exists cs => //.
    move=> off.
    rewrite (sub_concrete_slice_offset ok_cs1) (sub_concrete_slice_offset ok_cs2).
    move: ok_cs1; rewrite /sub_concrete_slice /=.
    case: ifP => // _ [<-] /=.
    rewrite Z.sub_add_distr.
    by apply hoff.
  case hle1: (odflt _ _) => //.
  case hle2: (odflt _ _) => //.
  case: z1 {ih1} => //.
  move=> hsuffix ok_cs1 ok_cs2.
  have [cs2' ok_cs2' hincl2] := sem_zone_cons_incl ok_cs2.
  move: hsuffix ok_cs1 ok_cs2'.
  rewrite /= /sem_slice.
  case: is_constP => //= ofs1.
  case: is_constP => //= len1.
  case: is_constP => //= ofs2.
  case: is_constP => //= len2.
  case: ifP => hif.
  + by move=> [?]; subst z.
  move=> [<-] [?] [?]; subst cs1 cs2'.
  eexists; first by reflexivity.
  move=> off + /(zbetween_concrete_sliceP hincl2).
  rewrite /offset_in_concrete_slice /= !zify.
  by lia.
Qed.

Lemma get_suffix_Some_Some_vars z1 z2 z :
  get_suffix z1 z2 = Some (Some z) ->
  Sv.Subset (read_zone z) (Sv.union (read_zone z1) (read_zone z2)).
Proof.
  elim: z1 z2 z => [|s1 z1 ih1] z2 z /=.
  + move=> [<-].
    by clear; SvD.fsetdec.
  case: z2 => [//|s2 z2].
  case: eqP => _.
  + move=> /ih1 /=.
    by clear; SvD.fsetdec.
  case: ifP => _ //.
  case: ifP => _ //.
  case: z1 {ih1} => [|//].
  case: is_const => // ofs1.
  case: is_const => // len1.
  case: is_const => // ofs2.
  case: is_const => // len2.
  case: ifP => _.
  + move=> [<-] /=.
    by clear; SvD.fsetdec.
  move=> [<-] /=.
  rewrite /read_slice /= /read_e /=.
  by clear; SvD.fsetdec.
Qed.

Lemma wf_status_clear_status_map_aux vme status z ty sl rmap x :
  wfr_WF rmap vme ->
  wf_status vme status ->
  wf_zone vme z ty sl ->
  wf_status vme (odflt Unknown (clear_status_map_aux rmap z x status)).
Proof.
  move=> hwfsr hwfs hwfz.
  rewrite /clear_status_map_aux.
  case heq: (let%opt _ := _ in get_suffix _ _) => [oz|//].
  case: oz heq => [z1|//].
  apply: obindP => sr hsr hsuffix.
  have hwf := hwfsr _ _ hsr.
  have [cs ok_cs _] := hwf.(wfsr_zone).
  have [cs' ok_cs' _] := hwfz.
  have: z1 = [::] \/ z1 <> [::].
  + by case: (z1); [left|right].
  case.
  + by move=> ->.
  move=> z1_nnil.
  have [cs1 ok_cs1 _] := get_suffix_Some_Some z1_nnil hsuffix ok_cs ok_cs'.
  by apply (wf_status_clear_status hwfs ok_cs1).
Qed.

Lemma wf_vars_status_clear_status_map_aux vars rmap z x status :
  wfr_VARS_ZONE vars rmap ->
  wf_vars_zone vars z ->
  wf_vars_status vars status ->
  wf_vars_status vars (odflt Unknown (clear_status_map_aux rmap z x status)).
Proof.
  move=> hvarsz z_vars status_vars.
  rewrite /clear_status_map_aux.
  case heq: (let%opt _ := _ in get_suffix _ _) => [oz|//].
  case: oz heq => [z1|//].
  apply: obindP => sr hsr hsuffix.
  apply (wf_vars_status_clear_status status_vars).
  have := get_suffix_Some_Some_vars hsuffix.
  have := hvarsz _ _ hsr.
  move: z_vars.
  rewrite /wf_vars_zone.
  by clear; SvD.fsetdec.
Qed.

Lemma valid_offset_clear_status_map_aux vme status rmap x sr z cs cs' off :
  wf_status vme status ->
  Mvar.get rmap.(var_region) x = Some sr ->
  sem_zone vme sr.(sr_zone) = ok cs ->
  sem_zone vme z = ok cs' ->
  0 <= off < cs.(cs_len) ->
  valid_offset vme (odflt Unknown (clear_status_map_aux rmap z x status)) off ->
  valid_offset vme status off /\
  ~ offset_in_concrete_slice cs' (cs.(cs_ofs) + off).
Proof.
  move=> hwfs hget ok_cs ok_cs' hoff.
  rewrite /clear_status_map_aux hget.
  case hsuffix: get_suffix => [z1|//].
  case: z1 hsuffix => [z1|] hsuffix /= hvalid; last first.
  + (* sr.(sr_zone) and z disjoint *)
    split=> //.
    have off_in: offset_in_concrete_slice cs (cs.(cs_ofs) + off).
    + by rewrite /offset_in_concrete_slice !zify; lia.
    move=> off_in'.
    have hdisj := get_suffix_Some_None hsuffix ok_cs ok_cs'.
    by apply (disjoint_concrete_sliceP hdisj off_in off_in').
  (* sr.(sr_zone) and z intersect *)
  have: z1 = [::] \/ z1 <> [::].
  + by case: (z1); [left|right].
  case.
  + by move=> ?; subst z1.
  move=> z1_nnil.
  have [cs1 ok_cs1 off_inter] :=
    get_suffix_Some_Some z1_nnil hsuffix ok_cs ok_cs'.
  have [{}hvalid off_nin] :=
    valid_offset_clear_status hwfs ok_cs1 hvalid.
  split=> //.
  have off_in: offset_in_concrete_slice cs (cs.(cs_ofs) + off).
  + by rewrite /offset_in_concrete_slice !zify; lia.
  move=> off_in'.
  have := off_inter _ off_in off_in'.
  by rewrite Z.add_simpl_l.
Qed.

Lemma eq_sub_region_val_same_region vme sr ty ofs sry ty' s2 mem2 rmap y statusy v :
  wf_sub_region vme sr ty ->
  sub_region_addr vme sr = ok ofs ->
  Mvar.get rmap.(var_region) y = Some sry ->
  wf_sub_region vme sry ty' ->
  sr.(sr_region) = sry.(sr_region) ->
  (forall al p ws,
    disjoint_zrange ofs (size_of ty) p (wsize_size ws) ->
    read mem2 al p ws = read (emem s2) al p ws) ->
  wf_status vme statusy ->
  eq_sub_region_val ty' vme (emem s2) sry statusy v ->
  eq_sub_region_val ty' vme mem2 sry (odflt Unknown (clear_status_map_aux rmap sr.(sr_zone) y statusy)) v.
Proof.
  move=> hwf haddr hsry hwfy hr hreadeq hwfsy [hread hty'].
  split=> // off ofsy w haddry hvalid /[dup] /get_val_byte_bound; rewrite hty' => hoff hget.
  have [cs ok_cs wf_cs] := hwf.(wfsr_zone).
  have := wunsigned_sub_region_addr hwf ok_cs.
  rewrite haddr => -[_ [<-] ok_ofs].
  have [csy ok_csy wf_csy] := hwfy.(wfsr_zone).
  have := wunsigned_sub_region_addr hwfy ok_csy.
  rewrite haddry => -[_ [<-] ok_ofsy].
  have hoff': 0 <= off < csy.(cs_len).
  + have := wf_csy.(wfcs_len).
    by lia.
  have [{}hvalid off_nin] :=
    valid_offset_clear_status_map_aux hwfsy hsry ok_csy ok_cs hoff' hvalid.
  rewrite -(hread _ _ _ haddry hvalid hget).
  apply hreadeq.
  apply not_between_U8_disjoint_zrange.
  + by apply (no_overflow_sub_region_addr hwf haddr).
  rewrite /between /zbetween wsize8 !zify.
  rewrite wunsigned_add; last first.
  + have := no_overflow_sub_region_addr hwfy haddry.
    rewrite /no_overflow zify.
    have := wunsigned_range ofsy.
    by lia.
  rewrite ok_ofs ok_ofsy -hr => hb.
  apply off_nin.
  rewrite /offset_in_concrete_slice !zify.
  have := wf_cs.(wfcs_len).
  by lia.
Qed.

Lemma is_align_sub_region_stkptr vme x s ofs ws cs f w :
  wf_stkptr x s ofs ws cs f ->
  sub_region_addr vme (sub_region_stkptr s ws cs) = ok w ->
  is_align w Uptr.
Proof.
  move=> hlocal.
  rewrite /sub_region_addr /= => -[<-].
  (* TODO: could wfs_offset_align be is_align z.(z_ofs) Uptr ?
     does it make sense ?
  *)
  apply: is_align_add hlocal.(wfs_offset_align).
  apply (is_align_m hlocal.(wfs_align_ptr)).
  rewrite -hlocal.(wfs_align).
  by apply (slot_align (sub_region_stkptr_wf vme hlocal).(wfr_slot)).
Qed.

Lemma check_writableP x r tt :
  check_writable x r = ok tt ->
  r.(r_writable).
Proof. by rewrite /check_writable; t_xrbindP. Qed.

Lemma set_wordP vme sr (x:var_i) ofs rmap al status ws rmap2 :
  wf_sub_region vme sr x.(vtype) ->
  sub_region_addr vme sr = ok ofs ->
  set_word rmap al sr x status ws = ok rmap2 ->
  [/\ sr.(sr_region).(r_writable),
      is_aligned_if al ofs ws &
      rmap2 = set_word_pure rmap sr x status].
Proof.
  move=> hwf ok_ofs; rewrite /set_word.
  by t_xrbindP=> /check_writableP hw /(check_alignP hwf ok_ofs) hal <-.
Qed.

Lemma get_status_map_setP rv r r' sm :
  get_status_map (Mr.set rv r' sm) r = if r' == r then sm else get_status_map rv r.
Proof. by rewrite /get_status_map Mr.setP; case: eqP. Qed.

Lemma is_unknownP status : is_unknown status -> status = Unknown.
Proof. by case: status. Qed.

Lemma get_status_setP sm x x' status :
  get_status (set_status sm x' status) x = if x' == x then status else get_status sm x.
Proof.
  rewrite /get_status /set_status.
  case h: is_unknown.
  + have -> := is_unknownP h.
    by rewrite Mvar.removeP; case: eq_op.
  by rewrite Mvar.setP; case: eq_op.
Qed.

Lemma clear_status_map_aux_unknown rmap z x :
  odflt Unknown (clear_status_map_aux rmap z x Unknown) = Unknown.
Proof.
  rewrite /clear_status_map_aux.
  by case: (let%opt _ := _ in get_suffix _ _) => // -[] // [] //.
Qed.

Lemma clear_status_map_aux_not_unknown rmap z x status :
  odflt Unknown (clear_status_map_aux rmap z x status) <> Unknown ->
  exists sr, Mvar.get rmap.(var_region) x = Some sr.
Proof.
  rewrite /clear_status_map_aux.
  case: Mvar.get => [sr|//] _.
  by exists sr.
Qed.

Lemma get_status_clear x rmap z sm :
  get_status (clear_status_map rmap z sm) x =
  odflt Unknown (clear_status_map_aux rmap z x (get_status sm x)).
Proof.
  rewrite /clear_status_map /get_status.
  rewrite Mvar.filter_mapP.
  by case: Mvar.get => //; rewrite clear_status_map_aux_unknown.
Qed.

Lemma get_var_status_set_word_status rmap sr x status r y :
  get_var_status (set_word_status rmap sr x status) r y =
    let statusy := get_var_status rmap r y in
    if sr.(sr_region) != r then
      statusy
    else
      if x == y then status
      else
        odflt Unknown (clear_status_map_aux rmap sr.(sr_zone) y statusy).
Proof.
  rewrite /set_word_status /get_var_status.
  rewrite get_status_map_setP.
  case: eqP => [->|//] /=.
  rewrite get_status_setP.
  by case: eq_op => //; rewrite get_status_clear.
Qed.

Lemma check_gvalid_set_word vme sr (x:var_i) rmap al status ws rmap2 y sry statusy :
  Mvar.get rmap.(var_region) x = Some sr ->
  wf_sub_region vme sr x.(vtype) ->
  set_word rmap al sr x status ws = ok rmap2 ->
  check_gvalid rmap2 y = Some (sry, statusy) ->
    [/\ ~ is_glob y, x = gv y :> var, sry = sr & statusy = status]
  \/
    [/\ ~ is_glob y, x <> gv y :> var, sr.(sr_region) = sry.(sr_region),
        Mvar.get rmap.(var_region) y.(gv) = Some sry &
        let statusy' := get_var_status rmap sry.(sr_region) y.(gv) in
        statusy = odflt Unknown (clear_status_map_aux rmap sr.(sr_zone) y.(gv) statusy')]
  \/
    [/\ ~ is_glob y -> x <> gv y :> var, sr.(sr_region) <> sry.(sr_region) &
        check_gvalid rmap y = Some (sry, statusy)].
Proof.
  move=> hsr hwf hset.
  have [ofs haddr] := wf_sub_region_sub_region_addr hwf.
  have [hw _ ->] := set_wordP hwf haddr hset.
  rewrite /check_gvalid /=.
  case: (@idP (is_glob y)) => hg.
  + case heq: Mvar.get => [[ofs' ws']|//] [<- <-] /=.
    right; right; split => //.
    move=> heqr.
    by move: hw; rewrite heqr.
  case hsry: Mvar.get => [sr'|//] [? <-]; subst sr'.
  rewrite get_var_status_set_word_status.
  case: (x =P gv y :> var).
  + move=> eq_xy.
    move: hsry; rewrite -eq_xy hsr => -[<-].
    rewrite eqxx.
    by left; split.
  move=> neq_xy.
  case: eqP => heqr.
  + by right; left; split.
  by right; right; split.
Qed.

(* This lemma is used for [set_sub_region] and [set_stack_ptr]. *)
Lemma mem_unchanged_write_slot vme m0 s1 s2 sr ty ofs mem2 :
  wf_sub_region vme sr ty ->
  sub_region_addr vme sr = ok ofs ->
  sr.(sr_region).(r_writable) ->
  (forall al p ws,
    disjoint_zrange ofs (size_of ty) p (wsize_size ws) ->
    read mem2 al p ws = read (emem s2) al p ws) ->
  mem_unchanged (emem s1) m0 (emem s2) ->
  mem_unchanged (emem s1) m0 mem2.
Proof.
  move=> hwf haddr hwritable hreadeq hunch p hvalid1 hvalid2 hdisj.
  rewrite (hunch _ hvalid1 hvalid2 hdisj).
  symmetry; apply hreadeq.
  apply (disjoint_zrange_incl_l (zbetween_sub_region_addr hwf haddr)).
  apply (hdisj _ hwf.(wfr_slot)).
  by rewrite hwf.(wfr_writable).
Qed.

(* This lemma is used both for [set_word] and [set_stack_ptr]. *)
Lemma wfr_STATUS_set_word_status rmap vme sr x status ty :
  wfr_WF rmap vme ->
  wf_sub_region vme sr ty ->
  wf_status vme status ->
  wfr_STATUS rmap vme ->
  wfr_STATUS (set_word_status rmap sr x status) vme.
Proof.
  move=> hwfsr hwf hwfs hwfst.
  move=> r y.
  rewrite get_var_status_set_word_status.
  case: eq_op => //=.
  case: eq_op => //.
  by apply: wf_status_clear_status_map_aux hwf.(wfsr_zone).
Qed.

Lemma wfr_VARS_STATUS_set_word_status vars (rmap:region_map) sr x status :
  wf_vars_zone vars sr.(sr_zone) ->
  wf_vars_status vars status ->
  wfr_VARS_ZONE vars rmap ->
  wfr_VARS_STATUS vars rmap ->
  wfr_VARS_STATUS vars (set_word_status rmap sr x status).
Proof.
  move=> sr_vars status_vars hvarsz hvarss.
  move=> r y.
  rewrite get_var_status_set_word_status.
  case: eq_op => //=.
  case: eq_op => //.
  by apply wf_vars_status_clear_status_map_aux.
Qed.

(* TODO: move? *)
Lemma mk_lvar_nglob x : ~ is_glob x -> mk_lvar x.(gv) = x.
Proof. by case: x => [? []]. Qed.

(* This lemma is used only for [set_word]. *)
Lemma wfr_VAL_set_word vars rmap vme s1 s2 sr (x:var_i) ofs mem2 al status ws (rmap2 : region_map) v :
  wf_rmap vars rmap vme s1 s2 ->
  Mvar.get rmap.(var_region) x = Some sr ->
  sub_region_addr vme sr = ok ofs ->
  (forall al p ws,
    disjoint_zrange ofs (size_slot x) p (wsize_size ws) ->
    read mem2 al p ws = read (emem s2) al p ws) ->
  set_word rmap al sr x status ws = ok rmap2 ->
  truncatable true (vtype x) v ->
  eq_sub_region_val x.(vtype) vme mem2 sr status (vm_truncate_val (vtype x) v) ->
  wfr_VAL rmap2 vme (with_vm s1 (evm s1).[x <- v]) (with_mem s2 mem2).
Proof.
  move=> hwfr hsr haddr hreadeq hset htr hval y sry statusy vy.
  have /wfr_wf hwf := hsr.
  move=> /(check_gvalid_set_word hsr hwf hset) [|[|]].
  + case: x htr hval {hsr hwf hreadeq hset} => x xii /= htr hval.
    move=> [? ? -> ->]; subst x.
    have [_ hty] := hval.
    rewrite get_gvar_eq //.
    by t_xrbindP => hd <-.
  + move=> [hnglob hneq heqr hsry /= ->].
    have := check_gvalid_lvar hsry; rewrite mk_lvar_nglob // => hgvalid.
    rewrite get_gvar_neq //; move=> /(wfr_val hgvalid).
    assert (hwfy := check_gvalid_wf wfr_wf hgvalid).
    assert (hwfsy := check_gvalid_wf_status wfr_status hgvalid).
    by apply (eq_sub_region_val_same_region hwf haddr hsry hwfy heqr hreadeq hwfsy).
  move=> [? hneqr hgvalid].
  rewrite get_gvar_neq //; move=> /(wfr_val hgvalid).
  assert (hwfy := check_gvalid_wf wfr_wf hgvalid).
  apply: (eq_sub_region_val_distinct_regions hwf haddr hwfy hneqr _ hreadeq).
  by case: (set_wordP hwf haddr hset).
Qed.

Lemma var_region_not_new rmap vme s2 x sr :
  wfr_PTR rmap vme s2 ->
  Mvar.get rmap.(var_region) x = Some sr ->
  ~ Sv.In x pmap.(vnew).
Proof. by move=> /[apply] -[_ [/wf_vnew ? _]]. Qed.

Lemma valid_pk_set_word_status vars rmap vme s1 s2 x sr ofs mem2 status y pk sry :
  wf_rmap vars rmap vme s1 s2 ->
  Mvar.get rmap.(var_region) x = Some sr ->
  sub_region_addr vme sr = ok ofs ->
  ~ Sv.In x pmap.(vnew) ->
  (forall al p ws,
    disjoint_zrange ofs (size_slot x) p (wsize_size ws) ->
    read mem2 al p ws = read (emem s2) al p ws) ->
  wf_local y pk ->
  valid_pk rmap vme s2 sry pk ->
  valid_pk (set_word_status rmap sr x status) vme (with_mem s2 mem2) sry pk.
Proof.
  move=> hwfr hsr haddr hnin hreadeq hlocal hpk.
  case: pk hlocal hpk => //= s ofs' ws' z f hlocal hpk.
  rewrite /check_stack_ptr get_var_status_set_word_status.
  case: eqP => heqr /=.
  + case: eqP => heq2.
    + by have := hlocal.(wfs_new); congruence.
    set status' := odflt Unknown _.
    move=> /is_validP hvalid.
    have hnunknown: status' <> Unknown by congruence.
    have [srf hsrf] := clear_status_map_aux_not_unknown hnunknown.
    by case (var_region_not_new wfr_ptr hsrf hlocal.(wfs_new)).
  move=> hvalid pofs ofsy haddrp haddry.
  rewrite -(hpk hvalid _ _ haddrp haddry).
  apply hreadeq.
  apply disjoint_zrange_sym.
  have /wfr_wf hwf := hsr.
  have hwfp := sub_region_stkptr_wf vme hlocal.
  apply: (distinct_regions_disjoint_zrange hwfp haddrp hwf haddr _ erefl).
  by apply not_eq_sym.
Qed.

Lemma wfr_PTR_set_sub_region vars rmap vme s1 s2 (x:var_i) sr ofs mem2 al status ws rmap2 :
  wf_rmap vars rmap vme s1 s2 ->
  Mvar.get rmap.(var_region) x = Some sr ->
  sub_region_addr vme sr = ok ofs ->
  (forall al p ws,
    disjoint_zrange ofs (size_slot x) p (wsize_size ws) ->
    read mem2 al p ws = read (emem s2) al p ws) ->
  set_word rmap al sr x status ws = ok rmap2 ->
  wfr_PTR rmap2 vme (with_mem s2 mem2).
Proof.
  move=> hwfr hsr haddr hreadeq hset y sry.
  have /wfr_wf hwf := hsr.
  have [_ _ ->] /= := set_wordP hwf haddr hset.
  move=> /wfr_ptr [pky [hly hpky]].
  exists pky; split=> //.
  have /wfr_ptr [_ [/wf_vnew hnnew _]] := hsr.
  by apply (valid_pk_set_word_status _ hwfr hsr haddr hnnew hreadeq (wf_locals hly) hpky).
Qed.

(* This lemma is used for [set_sub_region] and [set_stack_ptr]. *)
Lemma eq_mem_source_write_slot table rmap vme m0 s1 s2 sr ty ofs mem2:
  valid_state table rmap vme m0 s1 s2 ->
  wf_sub_region vme sr ty ->
  sub_region_addr vme sr = ok ofs ->
  (forall al p ws,
    disjoint_zrange ofs (size_of ty) p (wsize_size ws) ->
    read mem2 al p ws = read (emem s2) al p ws) ->
  eq_mem_source (emem s1) mem2.
Proof.
  move=> hvs hwf haddr hreadeq p hvp.
  rewrite (vs_eq_mem hvp).
  symmetry; apply hreadeq.
  apply (disjoint_zrange_incl_l (zbetween_sub_region_addr hwf haddr)).
  by apply (vs_disjoint hwf.(wfr_slot) hvp).
Qed.

(* We show that, under the right hypotheses, [set_word] preserves
   the [valid_state] invariant.
   This lemma is used both for words and arrays. *)
Lemma valid_state_set_word table rmap vme m0 s1 s2 sr (x:var_i) ofs mem2 al
    status ws (rmap2 : region_map) v :
  valid_state table rmap vme m0 s1 s2 ->
  Mvar.get rmap.(var_region) x = Some sr ->
  sub_region_addr vme sr = ok ofs ->
  stack_stable (emem s2) mem2 ->
  (validw mem2 =3 validw (emem s2)) ->
  (forall al p ws,
    disjoint_zrange ofs (size_slot x) p (wsize_size ws) ->
    read mem2 al p ws = read (emem s2) al p ws) ->
  wf_status vme status ->
  wf_vars_status table.(vars) status ->
  set_word rmap al sr x status ws = ok rmap2 ->
  truncatable true (vtype x) v ->
  eq_sub_region_val x.(vtype) vme mem2 sr status (vm_truncate_val (vtype x) v) ->
  valid_state (remove_binding table x) rmap2 vme m0 (with_vm s1 (evm s1).[x <- v]) (with_mem s2 mem2).
Proof.
  move=> hvs hsr haddr hss hvalideq hreadeq hwfs hvars hset htr heqval.
  have /wfr_wf hwf := hsr.
  have /wfr_ptr [pk [hlx hpk]] := hsr.
  case:(hvs) => hscs hvalid hdisj hincl hincl2 hunch hrip hrsp heqvm hwft hwfr heqmem hglobv htop.
  constructor => //=.
  + by move=> ??; rewrite hvalideq; apply hvalid.
  + by move=> ??; rewrite hvalideq; apply hincl.
  + by move=> ??; rewrite hvalideq; apply hincl2.
  + have [hwritable _ _] := set_wordP hwf haddr hset.
    by apply (mem_unchanged_write_slot hwf haddr hwritable hreadeq hunch).
  + move=> y hget; rewrite Vm.setP_neq /=; first by apply heqvm.
    by apply /eqP; rewrite /get_local in hlx; congruence.
  + by apply: wf_table_set_var hwft.
  + case: (hwfr) => hwfsr hwfst hvarsz hvarss hval hptr; split.
    + have [_ _ ->] := set_wordP hwf haddr hset.
      by move=> ?? /=; apply hwfsr.
    + have [addr ok_addr] := wf_sub_region_sub_region_addr hwf.
      have [_ _ ->] /= := set_wordP hwf ok_addr hset.
      by apply (wfr_STATUS_set_word_status _ hwfsr hwf hwfs hwfst).
    + have [_ _ ->] := set_wordP hwf haddr hset.
      by apply hvarsz.
    + have [_ _ ->] /= := set_wordP hwf haddr hset.
      by apply (wfr_VARS_STATUS_set_word_status _ (hvarsz _ _ hsr) hvars hvarsz hvarss).
    + by apply (wfr_VAL_set_word hwfr hsr haddr hreadeq hset htr heqval).
    by apply (wfr_PTR_set_sub_region hwfr hsr haddr hreadeq hset).
  + by apply (eq_mem_source_write_slot hvs hwf haddr hreadeq).
  by rewrite -(ss_top_stack hss).
Qed.

(* A version of [write_read8] easier to use. *)
Lemma write_read8_no_overflow mem1 mem2 al p ofs ws (w: word ws) :
  0 <= ofs /\ ofs + wsize_size ws <= wbase Uptr ->
  write mem1 al (p + wrepr _ ofs)%R w = ok mem2 ->
  forall k, 0 <= k < wbase Uptr ->
    read mem2 al (p + wrepr _ k)%R U8 =
      let i := k - ofs in
      if (0 <=? i) && (i <? wsize_size ws) then ok (LE.wread8 w i)
      else read mem1 al (p + wrepr _ k)%R U8.
Proof.
  move=> hofs hmem2 k hk.
  rewrite (write_read8 hmem2).
  rewrite subE {1}(GRing.addrC p) GRing.addrKA /=.
  rewrite wunsigned_sub_if.
  have hws := wsize_size_pos ws.
  rewrite !wunsigned_repr_small //; last by lia.
  case: (ZleP ofs k) => [//|hlt].
  case: (ZleP 0 (k - ofs)) => [|_]; first by lia.
  case: ZltP => [|_]; first by lia.
  by rewrite andFb andbF.
Qed.

(* Hypotheses are a bit restrictive but are those available in the proofs. *)
Lemma write_read8_sub_region vme sr ty addr ofs ws mem1 al (w:word ws) mem2 :
  wf_sub_region vme sr ty ->
  sub_region_addr vme sr = ok addr ->
  0 <= ofs /\ ofs + wsize_size ws <= size_of ty ->
  write mem1 al (addr + wrepr _ ofs)%R w = ok mem2 ->
  forall k, 0 <= k < size_of ty ->
    read mem2 al (addr + wrepr _ k)%R U8 =
      let i := k - ofs in
      if (0 <=? i) && (i <? wsize_size ws) then ok (LE.wread8 w i)
      else read mem1 al (addr + wrepr _ k)%R U8.
Proof.
  move=> hwf haddr hofs hmem2 k hk.
  have := no_overflow_sub_region_addr hwf haddr;
    rewrite /no_overflow !zify => hover.
  have ? := wunsigned_range addr.
  by apply: (write_read8_no_overflow _ hmem2); lia.
Qed.

Lemma zbetween_sub_region_addr_ofs vme sr ty addr ofs ws :
  wf_sub_region vme sr ty ->
  sub_region_addr vme sr = ok addr ->
  0 <= ofs /\ ofs + wsize_size ws <= size_of ty ->
  zbetween addr (size_of ty) (addr + wrepr _ ofs) (wsize_size ws).
Proof.
  move=> hwf haddr hofs.
  rewrite /zbetween !zify.
  rewrite wunsigned_add; first by lia.
  have := no_overflow_sub_region_addr hwf haddr.
  rewrite /no_overflow zify.
  have := wunsigned_range addr.
  have := wsize_size_pos ws.
  by lia.
Qed.

Lemma validw_sub_region_addr_ofs table rmap vme m0 s1 s2 sr ty addr ofs al ws :
  valid_state table rmap vme m0 s1 s2 ->
  wf_sub_region vme sr ty ->
  sub_region_addr vme sr = ok addr ->
  0 <= ofs /\ ofs + wsize_size ws <= size_of ty ->
  is_aligned_if al (addr + wrepr _ ofs)%R ws ->
  validw s2.(emem) al (addr + wrepr _ ofs)%R ws.
Proof.
  move=> hvs hwf haddr hbound hal.
  have /vs_slot_valid hptr := hwf.(wfr_slot).
  apply /validwP; split=> //.
  move=> k hk; rewrite (validw8_alignment Aligned); apply hptr; move: hk.
  apply: between_byte.
  + apply: no_overflow_incl (no_overflow_sub_region_addr hwf haddr).
    by apply (zbetween_sub_region_addr_ofs hwf haddr hbound).
  apply (zbetween_trans (zbetween_sub_region_addr hwf haddr)).
  by apply (zbetween_sub_region_addr_ofs hwf haddr hbound).
Qed.

Lemma wfr_VARS_ZONE_alloc_lval rmap r1 ty rmap2 r2 vars :
  alloc_lval pmap rmap r1 ty = ok (rmap2, r2) ->
  wfr_VARS_ZONE vars rmap ->
  wfr_VARS_ZONE vars rmap2.
Proof.
  rewrite /alloc_lval.
  case: r1 => //.
  + by move=> _ _ [<- _].
  + move=> x.
    case: get_local => [pk|]; last first.
    + by t_xrbindP=> _ <- _.
    case: is_word_type => [ws|//].
    case: ifP => // _.
    t_xrbindP=> sr /get_sub_regionP hsr {}rmap2 hrmap2 [_ _] _ [<- _].
    move: hrmap2; rewrite /set_word.
    by t_xrbindP=> _ _ <-.
  + by t_xrbindP=> _ _ _ _ _ _ _ _ <- _.
  t_xrbindP=> ??? x ?? _.
  case: get_local => [pk|]; last first.
  + by t_xrbindP=> _ <- _.
  t_xrbindP=> -[sr ?] /get_sub_region_statusP [hsr _].
  t_xrbindP=> {}rmap2 hrmap2 [_ _] _ [<- _].
  move: hrmap2; rewrite /set_word.
  by t_xrbindP=> _ _ <-.
Qed.

Lemma wfr_VARS_STATUS_alloc_lval rmap r1 ty rmap2 r2 vars :
  alloc_lval pmap rmap r1 ty = ok (rmap2, r2) ->
  wfr_VARS_ZONE vars rmap ->
  wfr_VARS_STATUS vars rmap ->
  wfr_VARS_STATUS vars rmap2.
Proof.
  rewrite /alloc_lval.
  case: r1 => //.
  + by move=> _ _ [<- _].
  + move=> x.
    case: get_local => [pk|]; last first.
    + by t_xrbindP=> _ <- _.
    case: is_word_type => [ws|//].
    case: ifP => // _.
    t_xrbindP=> sr /get_sub_regionP hsr {}rmap2 hrmap2 [_ _] _ [<- _].
    move: hrmap2; rewrite /set_word.
    t_xrbindP=> _ _ <-.
    move=> hvarsz hvarss.
    apply wfr_VARS_STATUS_set_word_status => //.
    by apply (hvarsz _ _ hsr).
  + by t_xrbindP=> _ _ _ _ _ _ _ _ <- _.
  t_xrbindP=> ??? x ?? _.
  case: get_local => [pk|]; last first.
  + by t_xrbindP=> _ <- _.
  t_xrbindP=> -[sr _] /get_sub_region_statusP [hsr ->].
  t_xrbindP=> {}rmap2 hrmap2 [_ _] _ [<- _].
  move: hrmap2; rewrite /set_word.
  t_xrbindP=> _ _ <-.
  move=> hvarsz hvarss.
  apply wfr_VARS_STATUS_set_word_status => //.
  by apply (hvarsz _ _ hsr).
Qed.

Lemma alloc_lvalP table rmap vme r1 r2 v ty m0 (s1 s2: estate) :
  alloc_lval pmap rmap r1 ty = ok r2 -> 
  valid_state table rmap vme m0 s1 s2 -> 
  type_of_val v = ty ->
  forall s1',
    write_lval true gd r1 v s1 = ok s1' ->
    exists2 s2',
      write_lval true [::] r2.2 v s2 = ok s2' &
      valid_state (remove_binding_lval table r1) r2.1 vme m0 s1' s2'.
Proof.
  move=> ha hvs ?; subst ty.
  case: r1 ha => //; rewrite /alloc_lval.
  (* Lnone *)
  + move=> vi ty1 [<-] /= s1' /write_noneP.
    by rewrite /write_none => - [-> -> ->]; exists s2 => //.

  (* Lvar *)
  + move=> x.
    case hlx: get_local => [pk | ]; last first.
    + t_xrbindP=> /check_diffP hnnew <- s1' /= /write_varP [-> hdb htr].
      eexists; first by apply: (write_var_truncate hdb htr).
      by apply: valid_state_set_var.
    case heq: is_word_type => [ws | //]; move /is_word_typeP : heq => hty.
    case htyv: subtype => //.
    t_xrbindP=> sr /get_sub_regionP hsr rmap2 hsetw [xi ofsi] ha [<-] /= s1'
      /write_varP [-> hdb htr] /=.
    have /wfr_wf hwf := hsr.
    have /wf_locals hlocal := hlx.
    have /wfr_ptr := hsr; rewrite hlx => -[_ [[<-] hpk]].
    have [wi ok_wi haddr] := addr_from_pkP hvs true hlocal hpk hwf ha.
    rewrite ok_wi /= truncate_word_u /=.
    have := htr; rewrite {1}hty =>
      /(vm_truncate_val_subtype_word hdb htyv) [w htrw -> /=].
    have hofs: 0 <= 0 /\ wsize_size ws <= size_slot x by rewrite hty /=; lia.
    have hvp: validw (emem s2) Aligned (wi + wrepr _ ofsi)%R ws.
    + have [_ halign _] := set_wordP hwf haddr hsetw.
      have := validw_sub_region_addr_ofs hvs hwf haddr hofs.
      rewrite wrepr0 GRing.addr0.
      by apply.
    have /writeV -/(_ w) [mem2 hmem2] := hvp.
    rewrite hmem2 /=; eexists; first by reflexivity.
    (* valid_state update word *)
    have [_ _ hset] := set_wordP hwf haddr hsetw.
    apply: (valid_state_set_word hvs hsr haddr _ _ _ _ _ hsetw) => //.
    + by apply (Memory.write_mem_stable hmem2).
    + by move=> ??; apply (write_validw_eq hmem2).
    + move=> al p ws''.
      rewrite hty => /disjoint_range_alt.
      exact: (writeP_neq _ hmem2).
    rewrite {2}hty htrw; split => //.
    rewrite /eq_sub_region_val_read haddr.
    move=> off _ ? [<-] _ hget.
    have /= hoff := get_val_byte_bound hget.
    rewrite -(GRing.addr0 (_+_))%R in hmem2.
    rewrite (write_read8_sub_region hwf haddr hofs hmem2) /= ?hty // Z.sub_0_r /=.
    move: (hoff); rewrite -!zify => ->.
    by rewrite -(get_val_byte_word _ hoff).

  (* Lmem *)
  + move=> al ws x e1 /=; t_xrbindP => /check_varP hx /check_diffP hnnew e1' /(alloc_eP hvs) he1 <-.
    move=> s1' xp ? hgx hxp w1 v1 /he1 he1' hv1 w hvw mem1 hmem1 <- /=.
    have := get_var_kindP hvs hx hnnew; rewrite /get_gvar /= => /(_ _ _ hgx) -> /=.
    have {}he1': sem_pexpr true [::] s2 e1' >>= to_pointer = ok w1.
    + have [ws1 [wv1 [? hwv1]]] := to_wordI hv1; subst.
      move: he1'; rewrite /truncate_val /= hwv1 /= => /(_ _ erefl) [] ve1' [] -> /=.
      by t_xrbindP=> w1' -> ? /=; subst w1'.
    rewrite he1' hxp /= hvw /=.
    have hvp1 := write_validw hmem1.
    have /valid_incl_word hvp2 := hvp1.
    have /writeV -/(_ w) [mem2 hmem2] := hvp2.
    rewrite hmem2 /=; eexists; first by reflexivity.
    (* valid_state update mem *)
    case:(hvs) => hscs hvalid hdisj hincl hincl2 hunch hrip hrsp heqvm hwft hwfr heqmem hglobv htop.
    constructor => //=.
    + move=> ??; rewrite (write_validw_eq hmem2); apply hvalid.
    + by move=> ???; rewrite (write_validw_eq hmem1); apply hdisj.
    + move=> ?; rewrite (write_validw_eq hmem1) (write_validw_eq hmem2); apply hincl.
    + move=> ?; rewrite (write_validw_eq hmem2); apply hincl2.
    + move=> p hvalid2; rewrite (write_validw_eq hmem1) => hvalid3 hdisj2.
      rewrite (hunch p hvalid2 hvalid3 hdisj2).
      symmetry; apply (writeP_neq _ hmem2).
      by apply (disjoint_range_valid_not_valid_U8 hvp1 hvalid3).
    + case: (hwfr) => hwfsr hwfst hvarsz hvarss hval hptr; split=> //.
      + move=> y sry statusy vy hgvalid hgy.
        assert (hwfy := check_gvalid_wf hwfsr hgvalid).
        have hreadeq := writeP_neq _ hmem2.
        have [ofsy haddry] := wf_sub_region_sub_region_addr hwfy.
        apply: (eq_sub_region_val_disjoint_zrange_ovf hreadeq haddry _ (hval _ _ _ _ hgvalid hgy)).
        have := disjoint_source_word hvs hwfy.(wfr_slot) hvp1.
        have := zbetween_sub_region_addr hwfy haddry.
        exact: zbetween_disjoint_zrange_ovf.
      move=> y sry hgy.
      have [pk [hgpk hvpk]] := hptr _ _ hgy; exists pk; split => //.
      case: pk hgpk hvpk => //= s ofs ws' z f hgpk hread hcheck pofs ofsy haddrp haddry.
      rewrite -(hread hcheck _ _ haddrp haddry).
      apply: (writeP_neq _ hmem2).
      assert (hwf' := sub_region_stkptr_wf vme (wf_locals hgpk)).
      have := disjoint_source_word hvs hwf'.(wfr_slot) hvp1.
      have := zbetween_sub_region_addr hwf' haddrp.
      exact: zbetween_disjoint_zrange_ovf.
    + move=> p; rewrite (write_validw_eq hmem1) => hv.
      apply: read_write_any_mem hmem1 hmem2.
      by apply heqmem.
    by rewrite -(ss_top_stack (Memory.write_mem_stable hmem2)).

  (* Laset *)
  move=> al aa ws x e1 /=; t_xrbindP => e1' /(alloc_eP hvs) he1.
  move=> hr2 s1'; apply: on_arr_varP => n t hty hxt.
  t_xrbindP => i1 v1 /he1 he1' hi1 w hvw t' htt' /write_varP [? hdb htr]; subst s1'.
  have {}he1 : sem_pexpr true [::] s2 e1' >>= to_int = ok i1.
  + have ? := to_intI hi1; subst.
    move: he1'; rewrite /truncate_val /= => /(_ _ erefl) [] ve1' [] -> /=.
    by t_xrbindP=> i1' -> ? /=; subst i1'.
  case hlx: get_local hr2 => [pk | ]; last first.
  + t_xrbindP=> /check_diffP hnnew <-.
    have /get_var_kindP -/(_ _ _ hnnew hxt) : get_var_kind pmap (mk_lvar x) = ok None.
    + by rewrite /get_var_kind /= hlx.
    rewrite /get_gvar /= => hxt2.
    rewrite he1 hxt2 /= hvw /= htt' /= (write_var_truncate hdb htr) //.
    by eexists; first reflexivity; apply: valid_state_set_var.
  t_xrbindP=> -[sr status] /get_sub_region_statusP [hsr ->].
  t_xrbindP=> rmap2 hset [xi ofsi] ha [<-] /=.
  have /wfr_wf hwf := hsr.
  have /wfr_ptr := hsr; rewrite hlx /= => -[_ [[<-] /= hpk]].
  have [wx -> /= haddr] := addr_from_pkP hvs true (wf_locals hlx) hpk hwf ha.
  rewrite (mk_ofsP aa ws ofsi he1) /= truncate_word_u /= hvw /=.
  have [hge0 hlen haa] := WArray.set_bound htt'.
  have hvp: validw (emem s2) al (wx + wrepr Uptr ofsi + wrepr _ (i1 * mk_scale aa ws))%R ws.
  + apply (validw_sub_region_addr_ofs hvs hwf haddr); first by rewrite hty.
    have [_ hal _] := set_wordP hwf haddr hset.
    case: al haa hal {htt' hset} => //= haa hal.
    apply: is_align_add; first by [].
    by rewrite WArray.arr_is_align.
  have /writeV -/(_ w) [mem2 hmem2] := hvp.
  rewrite Z.add_comm wrepr_add GRing.addrA hmem2 /=; eexists; first by reflexivity.
  (* valid_state update array *)
  have hofs: 0 <= i1 * mk_scale aa ws /\ i1 * mk_scale aa ws + size_of (sword ws) <= size_slot x.
  + by rewrite hty.
  have hvalideq := write_validw_eq hmem2.
  apply: (valid_state_set_word hvs hsr haddr  _ hvalideq _ _ _ hset htr) => //.
  + by apply (Memory.write_mem_stable hmem2).
  + move=> al' p ws' hdisj.
    apply (writeP_neq _ hmem2).
    apply: disjoint_range_alt.
    apply: disjoint_zrange_incl_l hdisj.
    by apply (zbetween_sub_region_addr_ofs hwf haddr).
  + by apply wfr_status.
  + by apply wfr_vars_status.
  have /vm_truncate_valE [_ ->]:= htr.
  split=> //.
  rewrite /eq_sub_region_val_read haddr.
  move=> off _ ? [<-] hvalid hget.
  have /= hoff := get_val_byte_bound hget.
  rewrite (read8_alignment al) (write_read8_sub_region hwf haddr hofs hmem2) /= ?hty //.
  move: hget; rewrite /= (write_read8 htt') WArray.subE /=.
  case: ifP => // hle.
  have hgvalid := check_gvalid_lvar hsr.
  assert (hval := wfr_val hgvalid hxt).
  case: hval => hread _.
  rewrite (read8_alignment Aligned).
  by apply hread.
Qed.

Lemma wfr_VARS_ZONE_alloc_lvals rmap rs1 tys rmap2 rs2 vars :
  alloc_lvals pmap rmap rs1 tys = ok (rmap2, rs2) ->
  wfr_VARS_ZONE vars rmap ->
  wfr_VARS_ZONE vars rmap2.
Proof.
  rewrite /alloc_lvals.
  elim: rs1 tys rmap rmap2 rs2 => [|r1 rs1 ih] [|ty tys] rmap rmap2 rs2 //=.
  + by move=> [<- _].
  t_xrbindP=> -[rmap1' r2] halloc [{}rmap2 {}rs2] /= hallocs <- _.
  move=> hvarsz1.
  have hvarsz1' := wfr_VARS_ZONE_alloc_lval halloc hvarsz1.
  by apply: ih hallocs hvarsz1'.
Qed.

Lemma wfr_VARS_STATUS_alloc_lvals rmap rs1 tys rmap2 rs2 vars :
  alloc_lvals pmap rmap rs1 tys = ok (rmap2, rs2) ->
  wfr_VARS_ZONE vars rmap ->
  wfr_VARS_STATUS vars rmap ->
  wfr_VARS_STATUS vars rmap2.
Proof.
  rewrite /alloc_lvals.
  elim: rs1 tys rmap rmap2 rs2 => [|r1 rs1 ih] [|ty tys] rmap rmap2 rs2 //=.
  + by move=> [<- _].
  t_xrbindP=> -[rmap1' r2] halloc [{}rmap2 {}rs2] /= hallocs <- _.
  move=> hvarsz1 hvarss1.
  have hvarsz1' := wfr_VARS_ZONE_alloc_lval halloc hvarsz1.
  have hvarss1' := wfr_VARS_STATUS_alloc_lval halloc hvarsz1 hvarss1.
  by apply: ih hallocs hvarsz1' hvarss1'.
Qed.

Lemma alloc_lvalsP table rmap vme r1 r2 vs ty m0 (s1 s2: estate) :
  alloc_lvals pmap rmap r1 ty = ok r2 ->
  valid_state table rmap vme m0 s1 s2 ->
  seq.map type_of_val vs = ty ->
  forall s1',
    write_lvals true gd s1 r1 vs = ok s1' ->
    exists2 s2',
      write_lvals true [::] s2 r2.2 vs = ok s2' &
      valid_state (foldl remove_binding_lval table r1) r2.1 vme m0 s1' s2'.
Proof.
  elim: r1 r2 rmap ty vs vme s1 s2 table => //= [|a l IH] r2 rmap [ | ty tys] // [ | v vs] //.
  + by move=> vme s1 s2 ? [<-] Hvalid _ s1' [<-]; exists s2.
  move=> vme s1 s2 table; t_xrbindP => -[a' r3] ha [l' r4] /IH hrec <-.
  move=> Hvalid [] hty htys s1' s1'' ha1 hl1.
  have [s2' hs2' vs2']:= alloc_lvalP ha Hvalid hty ha1.
  have [s2'' hs2'' vs2'']:= hrec _ _ _ _ _ vs2' htys _ hl1.
  by exists s2'' => //=; rewrite hs2'.
Qed.

Variable (P' : sprog).
Hypothesis P'_globs : P'.(p_globs) = [::].

Local Opaque arr_size.

Lemma get_var_status_set_move_status rv x r status ry y :
  get_var_status (set_move_status rv x r status) ry y =
    let statusy := get_var_status rv ry y in
    if r != ry then
      statusy
    else
      if x == y then status
      else statusy.
Proof.
  rewrite /set_move_status /get_var_status get_status_map_setP.
  case: eqP => //= <-.
  by rewrite get_status_setP.
Qed.

Lemma check_gvalid_set_move rmap x sr status y sry statusy :
  check_gvalid (set_move rmap x sr status) y = Some (sry, statusy) ->
    [/\ ~ is_glob y, x = gv y, sr = sry &
        statusy = status]
  \/
    [/\ ~ is_glob y -> x <> gv y &
        check_gvalid rmap y = Some (sry, statusy)].
Proof.
  rewrite /check_gvalid.
  case: (@idP (is_glob y)) => hg.
  + case heq: Mvar.get => [[ofs ws]|//] [<- <-].
    by right; split.
  rewrite Mvar.setP; case: eqP.
  + move=> -> [<- <-]; left; split=> //.
    by rewrite get_var_status_set_move_status !eq_refl.
  move=> hneq.
  case heq': Mvar.get => [sr'|//] [? <-]; subst sr'.
  right; split => //.
  rewrite get_var_status_set_move_status.
  case: eqP => [_|//].
  by move: hneq=> /eqP /negPf ->.
Qed.

Lemma type_of_get_gvar_array wdb gd vm x n (a : WArray.array n) :
  get_gvar wdb gd vm x = ok (Varr a) ->
  x.(gv).(vtype) = sarr n.
Proof. by move=> /get_gvar_compat; rewrite /compat_val /= orbF => -[_] /compat_typeEl. Qed.

Lemma is_stack_ptrP vpk s ofs ws z f :
  is_stack_ptr vpk = Some (s, ofs, ws, z, f) ->
  vpk = VKptr (Pstkptr s ofs ws z f).
Proof.
  case: vpk => [|[]] => //=.
  by move=> _ _ _ _ _ [-> -> -> -> ->].
Qed.

Lemma addr_from_vpk_pexprP table rmap vme m0 s1 s2 (x : var_i) vpk sr ty e1 ofs wdb :
  valid_state table rmap vme m0 s1 s2 ->
  wf_vpk x vpk ->
  valid_vpk rmap vme s2 x sr vpk ->
  wf_sub_region vme sr ty ->
  addr_from_vpk_pexpr pmap rmap x vpk = ok (e1, ofs) ->
  exists2 w,
    sem_pexpr wdb [::] s2 e1 >>= to_pointer = ok w &
    sub_region_addr vme sr = ok (w + wrepr _ ofs)%R.
Proof.
  move=> hvs hwfpk hpk hwf.
  rewrite /addr_from_vpk_pexpr.
  case heq: is_stack_ptr => [[[[[s ws] ofs'] z] f]|]; last first.
  + by t_xrbindP=> -[x' ofs'] /(addr_from_vpkP hvs wdb hwfpk hpk hwf) haddr <- <-.
  move /is_stack_ptrP in heq; subst vpk.
  rewrite /= in hpk hwfpk.
  t_xrbindP=> /hpk hread <- <- /=.
  have [addr haddr] := wf_sub_region_sub_region_addr hwf.
  have haddrp := sub_region_addr_stkptr vme hwfpk.
  rewrite
    truncate_word_u /=
    /get_var vs_rsp /= orbT /=
    truncate_word_u /=
    (hread _ _ haddrp haddr) /=
    truncate_word_u.
  eexists; first by reflexivity.
  by rewrite wrepr0 GRing.addr0.
Qed.

(* Alternative form of cast_get8, easier to use in our case *)
Lemma cast_get8 len1 len2 (m : WArray.array len2) (m' : WArray.array len1) :
  WArray.cast len1 m = ok m' ->
  forall k w,
    read m' Aligned k U8 = ok w ->
    read m Aligned k U8 = ok w.
Proof.
  move=> hcast k w.
  move=> /[dup]; rewrite -{1}get_read8 => /WArray.get_valid8 /WArray.in_boundP => hbound.
  rewrite (WArray.cast_get8 hcast).
  by case: hbound => _ /ZltP ->.
Qed.

Lemma wfr_WF_set vme sr x rmap rmap2 :
  wf_sub_region vme sr x.(vtype) ->
  rmap2.(var_region) = Mvar.set rmap.(var_region) x sr ->
  wfr_WF rmap vme ->
  wfr_WF rmap2 vme.
Proof.
  move=> hwf hrmap2 hwfr y sry.
  rewrite hrmap2 Mvar.setP.
  by case: eqP; [congruence|auto].
Qed.

Lemma wfr_STATUS_set_move_status vme status rv x r :
  wf_status vme status ->
  wfr_STATUS rv vme ->
  wfr_STATUS (set_move_status rv x r status) vme.
Proof.
  move=> hwfs hwfst.
  move=> ry y.
  rewrite get_var_status_set_move_status.
  case: eq_op => //=.
  by case: eq_op.
Qed.

Lemma wfr_VARS_ZONE_set_move vars rmap x sr status :
  wf_vars_zone vars sr.(sr_zone) ->
  wfr_VARS_ZONE vars rmap ->
  wfr_VARS_ZONE vars (set_move rmap x sr status).
Proof.
  move=> hvars hvarsz.
  move=> y sry /=.
  rewrite Mvar.setP.
  case: eqP => _.
  + by move=> [<-].
  by apply hvarsz.
Qed.

Lemma wfr_VARS_STATUS_set_move_status vars rv x r status :
  wf_vars_status vars status ->
  wfr_VARS_STATUS vars rv ->
  wfr_VARS_STATUS vars (set_move_status rv x r status).
Proof.
  move=> hvars hvarss.
  move=> ry y.
  rewrite get_var_status_set_move_status.
  case: eq_op => //=.
  by case: eq_op.
Qed.

Lemma wfr_VAL_set_move rmap vme s1 s2 x sr status v :
  truncatable true (vtype x) v ->
  eq_sub_region_val x.(vtype) vme (emem s2) sr status
    (vm_truncate_val (vtype x) v) ->
  wfr_VAL rmap vme s1 s2 ->
  wfr_VAL (set_move rmap x sr status) vme (with_vm s1 (evm s1).[x <- v]) s2.
Proof.
  move=> htr heqval hval y sry bytesy vy /check_gvalid_set_move [].
  + by move=> [? ? <- ->]; subst x; rewrite get_gvar_eq //; t_xrbindP => hd <-.
  by move=> [? hgvalid]; rewrite get_gvar_neq => //; apply hval.
Qed.

Lemma valid_pk_set_move (rmap:region_map) vme x sr status s2 y pky sry :
  ~ Sv.In x pmap.(vnew) ->
  wf_local y pky ->
  valid_pk rmap vme s2 sry pky ->
  valid_pk (set_move rmap x sr status) vme s2 sry pky.
Proof.
  move=> hnnew hlocal.
  case: pky hlocal => //=.
  move=> s ofs ws z f hlocal.
  rewrite /check_stack_ptr get_var_status_set_move_status.
  case: eqP => [_|//].
  case: eqP => //.
  by have := hlocal.(wfs_new); congruence.
Qed.

Lemma wfr_PTR_set_move (rmap : region_map) vme s2 x pk sr status :
  get_local pmap x = Some pk ->
  valid_pk rmap vme s2 sr pk ->
  wfr_PTR rmap vme s2 ->
  wfr_PTR (set_move rmap x sr status) vme s2.
Proof.
  move=> hlx hpk hptr y sry.
  have /wf_vnew hnnew := hlx.
  rewrite Mvar.setP; case: eqP.
  + move=> <- [<-].
    exists pk; split=> //.
    by apply (valid_pk_set_move _ _ hnnew (wf_locals hlx) hpk).
  move=> _ /hptr {pk hlx hpk} [pk [hly hpk]].
  exists pk; split=> //.
  by apply (valid_pk_set_move _ _ hnnew (wf_locals hly) hpk).
Qed.

(* There are several lemmas about [set_move] and [valid_state], and all are useful. *)
Lemma valid_state_set_move table rmap vme m0 s1 s2 x sr status pk v :
  valid_state table rmap vme m0 s1 s2 ->
  wf_sub_region vme sr x.(vtype) ->
  wf_status vme status ->
  wf_vars_zone table.(vars) sr.(sr_zone) ->
  wf_vars_status table.(vars) status ->
  get_local pmap x = Some pk ->
  valid_pk rmap.(region_var) vme s2 sr pk ->
  truncatable true (vtype x) v ->
  eq_sub_region_val x.(vtype) vme (emem s2) sr status (vm_truncate_val (vtype x) v) ->
  valid_state (remove_binding table x) (set_move rmap x sr status) vme m0 (with_vm s1 (evm s1).[x <- v]) s2.
Proof.
  move=> hvs hwf hwfs sr_vars status_vars hlx hpk htr heqval.
  case:(hvs) => hscs hvalid hdisj hincl hincl2 hunch hrip hrsp heqvm hwft hwfr heqmem hglobv htop.
  constructor=> //=.
  + move=> y hget; rewrite Vm.setP_neq; first by apply heqvm.
    by apply /eqP; rewrite /get_local in hlx; congruence.
  + by apply wf_table_set_var.
  case: (hwfr) => hwfsr hwfst hvarsz hvarss hval hptr; split.
  + by apply: (wfr_WF_set hwf _ hwfsr).
  + by apply (wfr_STATUS_set_move_status _ _ hwfs hwfst).
  + by apply (wfr_VARS_ZONE_set_move sr_vars hvarsz).
  + by apply (wfr_VARS_STATUS_set_move_status _ _ status_vars hvarss).
  + by apply (wfr_VAL_set_move htr heqval hval).
  by apply (wfr_PTR_set_move hlx hpk hptr).
Qed.

Lemma valid_state_set_move_regptr table rmap vme m0 s1 s2 x sr status v p addr :
  valid_state table rmap vme m0 s1 s2 ->
  wf_sub_region vme sr x.(vtype) ->
  sub_region_addr vme sr = ok addr ->
  wf_status vme status ->
  wf_vars_zone table.(vars) sr.(sr_zone) ->
  wf_vars_status table.(vars) status ->
  get_local pmap x = Some (Pregptr p) ->
  truncatable true (vtype x) v ->
  eq_sub_region_val x.(vtype) vme (emem s2) sr status (vm_truncate_val (vtype x) v) ->
  valid_state (remove_binding table x) (set_move rmap x sr status) vme m0
       (with_vm s1 (evm s1).[x <- v])
       (with_vm s2 (evm s2).[p <- Vword addr]).
Proof.
  move=> hvs hwf haddr hwfs sr_vars status_vars hlx htr heqval.
  have /wf_locals /= hlocal := hlx.
  case:(hvs) => hscs hvalid hdisj hincl hincl2 hunch hrip hrsp heqvm hwft hwfr heqmem hglobv htop.
  constructor=> //=.
  + rewrite Vm.setP_neq //; apply /eqP.
    by apply hlocal.(wfr_not_vrip).
  + rewrite Vm.setP_neq //; apply /eqP.
    by apply hlocal.(wfr_not_vrsp).
  + move=> y hget hnnew.
    rewrite Vm.setP_neq; last by apply/eqP; rewrite /get_local in hlx; congruence.
    rewrite Vm.setP_neq; last by apply/eqP; have := hlocal.(wfr_new); congruence.
    by apply heqvm.
  + by apply wf_table_set_var.
  case: (hwfr) => hwfsr hwfst hvarsz hvarss hval hptr; split.
  + by apply: (wfr_WF_set hwf _ hwfsr).
  + by apply (wfr_STATUS_set_move_status _ _ hwfs hwfst).
  + by apply (wfr_VARS_ZONE_set_move sr_vars hvarsz).
  + by apply (wfr_VARS_STATUS_set_move_status _ _ status_vars hvarss).
  + by apply (wfr_VAL_set_move htr heqval hval).
  move=> y sry.
  have htrp : truncatable true (vtype p) (Vword addr).
  + rewrite hlocal.(wfr_rtype).
    by apply (truncatable_type_of true (Vword addr)).
  rewrite Mvar.setP; case: eqP.
  + move=> <- [<-].
    exists (Pregptr p); split=> //=.
    rewrite haddr => _ [<-].
    by rewrite Vm.setP_eq // vm_truncate_val_eq // hlocal.(wfr_rtype).
  move=> hneq /hptr [pk [hly hpk]].
  exists pk; split=> //.
  case: pk hly hpk => //=.
  + move=> p2 hly.
    rewrite Vm.setP_neq //.
    by apply/eqP/(hlocal.(wfr_distinct) hly hneq).
  move=> s ofs ws z f hly.
  rewrite /check_stack_ptr get_var_status_set_move_status.
  case: eqP => [_|//].
  case: eqP => //.
  have /is_sarrP [n hty] := hlocal.(wfr_type).
  have /wf_locals /wfs_new := hly.
  by have /wf_vnew := hlx; congruence.
Qed.

(* For stack ptr, we call set_stack_ptr (set_move ...) ..., so set_stack_ptr is
   called on a rmap which does not satisfy valid_state, nor even wfr_PTR.
   But it satisfies
     (forall x sr, Mvar.get rmap.(var_region) x = Some sr -> ~ Sv.In x pmap.(vnew))
   and this is sufficient. *)

(* close to check_gvalid_set_word, but different hypotheses *)
Lemma check_gvalid_set_stack_ptr rmap s ws cs f y sry statusy :
  (forall x sr, Mvar.get rmap.(var_region) x = Some sr -> ~ Sv.In x pmap.(vnew)) ->
  Sv.In f pmap.(vnew) ->
  check_gvalid (set_stack_ptr rmap s ws cs f) y = Some (sry, statusy) ->
  [/\ ~ is_glob y, f <> gv y, (sub_region_stkptr s ws cs).(sr_region) = sry.(sr_region),
        Mvar.get rmap.(var_region) y.(gv) = Some sry &
        let statusy' := get_var_status rmap sry.(sr_region) y.(gv) in
        statusy = odflt Unknown (clear_status_map_aux rmap (sub_region_stkptr s ws cs).(sr_zone) y.(gv) statusy')]
  \/
    [/\ ~ is_glob y -> f <> gv y, (sub_region_stkptr s ws cs).(sr_region) <> sry.(sr_region) &
        check_gvalid rmap y = Some (sry, statusy)].
Proof.
  move=> hnnew hnew.
  rewrite /check_gvalid /=.
  case: (@idP (is_glob y)) => hg.
  + case heq: Mvar.get => [[ofs' ws']|//] [<- <-].
    by right; split.
  case hsry: Mvar.get => [sr|//] [? <-]; subst sr.
  have hneq: f <> y.(gv).
  + by move /hnnew : hsry; congruence.
  rewrite get_var_status_set_word_status.
  have /eqP /negPf -> /= := hneq.
  case: eqP => heqr /=.
  + by left; split.
  by right; split.
Qed.

Lemma valid_pk_set_stack_ptr (rmap : region_map) vme s2 x s ofs ws cs f paddr mem2 y pky sry :
  (forall x sr, Mvar.get rmap.(var_region) x = Some sr -> ~ Sv.In x pmap.(vnew)) ->
  wf_stkptr x s ofs ws cs f ->
  sub_region_addr vme (sub_region_stkptr s ws cs) = ok paddr ->
  (forall al p ws,
    disjoint_range paddr Uptr p ws ->
    read mem2 al p ws = read (emem s2) al p ws) ->
  x <> y ->
  get_local pmap y = Some pky ->
  valid_pk rmap vme s2 sry pky ->
  valid_pk (set_stack_ptr rmap s ws cs f) vme (with_mem s2 mem2) sry pky.
Proof.
  move=> hnnew hlocal hpaddr hreadeq hneq.
  case: pky => //= sy ofsy wsy csy fy hly hpky.
  have hwf := sub_region_stkptr_wf vme hlocal.
  assert (hwfy := sub_region_stkptr_wf vme (wf_locals hly)).
  rewrite /check_stack_ptr get_var_status_set_word_status.
  case: eqP => heqr /=.
  + have hneqf := hlocal.(wfs_distinct) hly hneq.
    have /eqP /negPf -> := hneqf.
    rewrite /clear_status_map_aux.
    case heq: Mvar.get => [srfy|//].
    (* pseudo-variables are not in var_region! We are imprecise, but the proof
       is easy. Cf. comment on clear_status_map_aux *)
    by case: (hnnew _ _ heq (wf_locals hly).(wfs_new)).
  move=> hcheck paddry addry hpaddry haddry.
  rewrite -(hpky hcheck _ _ hpaddry haddry).
  apply hreadeq.
  by apply (distinct_regions_disjoint_zrange hwf hpaddr hwfy hpaddry heqr erefl).
Qed.

(* For stack ptr, we call both set_move and set_stack_ptr. *)
Lemma valid_state_set_stack_ptr table rmap vme m0 s1 s2 x s ofs ws cs f paddr mem2 sr addr status v :
  valid_state table rmap vme m0 s1 s2 ->
  wf_sub_region vme sr x.(vtype) ->
  sub_region_addr vme sr = ok addr ->
  wf_status vme status ->
  wf_vars_zone table.(vars) sr.(sr_zone) ->
  wf_vars_status table.(vars) status ->
  get_local pmap x = Some (Pstkptr s ofs ws cs f) ->
  sub_region_addr vme (sub_region_stkptr s ws cs) = ok paddr ->
  stack_stable (emem s2) mem2 ->
  validw mem2 =3 validw (emem s2) ->
  (forall al p ws,
    disjoint_range paddr Uptr p ws ->
    read mem2 al p ws = read (emem s2) al p ws) ->
  read mem2 Aligned paddr Uptr = ok addr ->
  truncatable true (vtype x) v ->
  eq_sub_region_val x.(vtype) vme (emem s2) sr status (vm_truncate_val (vtype x) v) ->
  valid_state
    (remove_binding table x)
    (set_stack_ptr (set_move rmap x sr status) s ws cs f)
    vme m0 (with_vm s1 (evm s1).[x <- v]) (with_mem s2 mem2).
Proof.
  move=> hvs hwf haddr hwfs sr_vars status_vars hlx hpaddr hss hvalideq hreadeq hreadptr htr heqval.
  have /wf_locals hlocal := hlx.
  have hwf' := sub_region_stkptr_wf vme hlocal.
  case:(hvs) => hscs hvalid hdisj hincl hincl2 hunch hrip hrsp heqvm hwft hwfr heqmem hglobv htop.
  constructor=> //=.
  + by move=> ??; rewrite hvalideq; apply hvalid.
  + by move=> ??; rewrite hvalideq; apply hincl.
  + by move=> ??; rewrite hvalideq; apply hincl2.
  + by apply (mem_unchanged_write_slot hwf' hpaddr refl_equal hreadeq hunch).
  + move=> y hget; rewrite Vm.setP_neq; first by apply heqvm.
    by apply/eqP; rewrite /get_local in hlx; congruence.
  + by apply wf_table_set_var.
  case: (hwfr) => hwfsr hwfst hvarsz hvarss hval hptr.
  have hwfsr': wfr_WF (set_move rmap x sr status) vme.
  + by apply: (wfr_WF_set hwf _ hwfsr).
  have hwfst': wfr_STATUS (set_move rmap x sr status) vme.
  + by apply (wfr_STATUS_set_move_status _ _ hwfs hwfst).
  have hvarsz': wfr_VARS_ZONE table.(vars) (set_move rmap x sr status).
  + by apply (wfr_VARS_ZONE_set_move sr_vars hvarsz).
  have hvarss': wfr_VARS_STATUS table.(vars) (set_move rmap x sr status).
  + by apply (wfr_VARS_STATUS_set_move_status _ _ status_vars hvarss).
  have hval': wfr_VAL (set_move rmap x sr status) vme (with_vm s1 (evm s1).[x <- v]) s2.
  + by apply (wfr_VAL_set_move htr heqval hval).
  have hnnew: forall y' sry',
    Mvar.get (var_region (set_move rmap x sr status)) y' = Some sry' ->
    ~ Sv.In y' (vnew pmap).
  + move=> y' sry' /=.
    rewrite Mvar.setP.
    case: eqP.
    + by move=> <- _; apply (wf_vnew hlx).
    by move=> _; apply (var_region_not_new hptr).
  split=> //.
  + by apply: (wfr_STATUS_set_word_status _ hwfsr' hwf' _ hwfst').
  + apply wfr_VARS_STATUS_set_word_status => //.
    rewrite /wf_vars_zone /= /read_slice /= /read_e /=.
    by clear; SvD.fsetdec.
  + move=> y sry statusy vy /=.
    move=> /(check_gvalid_set_stack_ptr hnnew hlocal.(wfs_new)) [].
    + move=> [hnglob hneq heqr hsry /= ->] hgety.
      have := check_gvalid_lvar hsry; rewrite mk_lvar_nglob // => hgvalidy.
      have /= hwfy := check_gvalid_wf hwfsr' hgvalidy.
      assert (heqvaly := hval' _ _ _ _ hgvalidy hgety).
      by apply: (eq_sub_region_val_same_region hwf' hpaddr hsry hwfy heqr hreadeq _ heqvaly).
    move=> [? hneqr hgvalidy] hgety.
    have /= hwfy := check_gvalid_wf hwfsr' hgvalidy.
    assert (heqvaly := hval' _ _ _ _ hgvalidy hgety).
    by apply (eq_sub_region_val_distinct_regions hwf' hpaddr hwfy hneqr erefl hreadeq heqvaly).
  + move=> y sry.
    rewrite [Mvar.get _ _]/= Mvar.setP.
    case: eqP.
    + move=> <- [<-].
      exists (Pstkptr s ofs ws cs f); split=> //=.
      by rewrite haddr hpaddr => _ _ _ [<-] [<-].
    move=> hneq /wfr_ptr [pky [hly hpky]].
    exists pky; split=> //.
    apply (valid_pk_set_stack_ptr hnnew hlocal hpaddr hreadeq hneq hly).
    by apply (valid_pk_set_move sr status (wf_vnew hlx) (wf_locals hly) hpky).
  + by apply (eq_mem_source_write_slot hvs hwf' hpaddr hreadeq).
  by rewrite -(ss_top_stack hss).
Qed.

(* Just like set_word, set_move_sub does not update the var_region part of the
   rmap. It takes a region and a variable as arguments. It makes sense only
   if the region is the one associated to the variable in var_region. We add
   this as an hypothesis. *)
Lemma check_gvalid_set_move_sub rmap sr x statusx ofs len substatus y sry statusy :
  Mvar.get rmap.(var_region) x = Some sr ->
  check_gvalid (set_move_sub rmap sr.(sr_region) x statusx ofs len substatus) y = Some (sry, statusy) ->
    [/\ ~ is_glob y, x = gv y, sry = sr & statusy = insert_status x statusx ofs len substatus]
  \/
    [/\ ~ is_glob y -> x <> gv y &
        check_gvalid rmap y = Some (sry, statusy)].
Proof.
  move=> hsr.
  rewrite /check_gvalid /=.
  case: (@idP (is_glob y)) => hg.
  + case heq: Mvar.get => [[ofs' ws]|//] [<- <-] /=.
    by right; split.
  case hsry: Mvar.get => [sr'|//] [? <-]; subst sr'.
  rewrite get_var_status_set_move_status.
  case: (x =P y.(gv)).
  + move=> eq_xy.
    move: hsry; rewrite -eq_xy hsr => -[<-].
    rewrite eqxx.
    by left; split.
  move=> neq_xy.
  right; split=> //=.
  by rewrite if_same.
Qed.

Lemma incl_interval_remove_sub_interval i s :
  incl_interval (remove_sub_interval i s) i.
Proof.
  elim: i => [//|s1 i ih] /=.
  case: eqP => _.
  + by apply incl_interval_cons.
  case: ifP => _.
  + by apply incl_interval_refl.
  have hsub: incl_interval (s1 :: remove_sub_interval i s) (s1 :: i).
  + rewrite /= mem_head /=.
    apply: (incl_interval_trans ih (incl_interval_cons _ _)).
  case: is_const => [ofs|//].
  case: is_const => [len|//].
  case: is_const => [ofs1|//].
  case: is_const => [len1|//].
  case: ifP => _ //.
  by apply: (incl_interval_trans ih (incl_interval_cons _ _)).
Qed.

Lemma wf_interval_remove_sub_interval vme i s :
  wf_interval vme i ->
  wf_interval vme (remove_sub_interval i s).
Proof.
  apply incl_interval_wf_interval.
  by apply incl_interval_remove_sub_interval.
Qed.

Lemma incl_interval_read_interval i1 i2 :
  incl_interval i1 i2 ->
  Sv.Subset (read_interval i1) (read_interval i2).
Proof.
  elim: i1 => [|s1 i1 ih1] /=.
  + move=> _.
    by clear; SvD.fsetdec.
  move=> /andP [hin {}/ih1].
  have: Sv.Subset (read_slice s1) (read_interval i2).
  + elim: i2 s1 hin => [//|s2 i2 ih2] s1 /=.
    rewrite in_cons.
    case/orP.
    + move=> /eqP <-.
      by clear; SvD.fsetdec.
    move=> /ih2.
    by clear; SvD.fsetdec.
  by clear; SvD.fsetdec.
Qed.

Lemma remove_sub_interval_vars i s :
  Sv.Subset (read_interval (remove_sub_interval i s)) (read_interval i).
Proof.
  apply incl_interval_read_interval.
  by apply incl_interval_remove_sub_interval.
Qed.

(* the only useful lemma, we just need correctness *)
Lemma remove_sub_interval_1 vme i s cs off :
  sem_slice vme s = ok cs ->
  valid_offset_interval vme (remove_sub_interval i s) off ->
  ~ offset_in_concrete_slice cs off ->
  valid_offset_interval vme i off.
Proof.
  move=> ok_cs off_valid off_nin_cs ci ok_ci off_in_ci.
  have [ci2 ok_ci2]:
    exists ci, mapM (sem_slice vme) (remove_sub_interval i s) = ok ci.
  + apply wf_interval_remove_sub_interval.
    by exists ci.
  move: off_valid; rewrite /valid_offset_interval ok_ci2 => /(_ _ erefl).
  apply; move: off_in_ci off_nin_cs.
  elim: i ci ci2 ok_ci ok_ci2 => [|s' i ih] ci ci2 /=.
  + by move=> [<-] [<-].
  t_xrbindP=> cs' ok_cs' {}ci ok_ci <- /=.
  case: eqP => [?|_].
  + subst s'.
    move: ok_cs'; rewrite ok_cs => -[<-].
    rewrite ok_ci => -[<-].
    by case/orP.
  case: (@idP (odflt _ _)) => [hle|_].
  + by rewrite /= ok_cs' ok_ci /= => -[<-] /=.
  have h:
    mapM (sem_slice vme) (s' :: remove_sub_interval i s) = ok ci2 ->
    offset_in_concrete_slice cs' off || offset_in_concrete_interval ci off ->
    ~ offset_in_concrete_slice cs off → offset_in_concrete_interval ci2 off.
  + rewrite /= ok_cs' /=.
    t_xrbindP=> {}ci2 ok_ci2 <-.
    case/orP.
    + by move=> hoff _ /=; apply /orP; left.
    move=> hoff hnoff /=; apply /orP; right.
    by apply (ih _ _ ok_ci ok_ci2 hoff hnoff).
  move: ok_cs ok_cs'; rewrite {1 2}/sem_slice.
  case: is_constP => // ofs.
  case: is_constP => // len.
  case: is_constP => // ofs'.
  case: is_constP => // len'.
  case: ifP => //.
  move=> /= hb ok_cs ok_cs' ok_ci2.
  case/orP.
  + move: ok_cs ok_cs' => [<-] [<-] /= hoff [].
    by apply
      (zbetween_concrete_sliceP
        (cs1 := {| cs_ofs := _ |}) (cs2 := {| cs_ofs := _ |}) hb hoff).
  by apply: ih ok_ci ok_ci2.
Qed.

Lemma wf_status_fill_status vme status s :
  wf_status vme status ->
  wf_status vme (fill_status status s).
Proof.
  move=> hwfs.
  rewrite /fill_status.
  case: status hwfs => //= i i_wf.
  case: {1}remove_sub_interval => //= _ _.
  by apply (wf_interval_remove_sub_interval _ i_wf).
Qed.

Lemma wf_vars_status_fill_status vars status s :
  wf_vars_status vars status ->
  wf_vars_status vars (fill_status status s).
Proof.
  case: status => //= i i_vars.
  case heq: {1}remove_sub_interval => //=.
  have := @remove_sub_interval_vars i s.
  move: i_vars; rewrite /wf_vars_interval.
  by clear; SvD.fsetdec.
Qed.

Lemma valid_offset_fill_status vme s cs status off :
  wf_status vme status ->
  sem_slice vme s = ok cs ->
  valid_offset vme (fill_status status s) off ->
  ~ offset_in_concrete_slice cs off ->
  valid_offset vme status off.
Proof.
  case: status => //= i i_wf ok_cs off_valid.
  apply (remove_sub_interval_1 ok_cs).
  case: remove_sub_interval off_valid => //=.
  by move=> _ _ /= [<-].
Qed.

Lemma wf_status_insert_status vme status substatus ofs ofsi len leni x :
  wf_status vme status ->
  wf_status vme substatus ->
  sem_sexpr vme ofs >>= to_int = ok ofsi ->
  sem_sexpr vme len >>= to_int = ok leni ->
  wf_status vme (insert_status x status ofs len substatus).
Proof.
  move=> hwfs hwfs' ok_ofsi ok_leni.
  rewrite /insert_status.
  case: ifP => // _.
  case: ifP => _.
  + by apply (wf_status_fill_status _ hwfs).
  have ok_cs:
    sem_zone vme [:: {| ss_ofs := ofs; ss_len := len |}] =
      ok {| cs_ofs := ofsi; cs_len := leni |}.
  + by rewrite /= /sem_slice /= ok_ofsi ok_leni /=.
  by apply (wf_status_clear_status hwfs ok_cs).
Qed.

Lemma wf_vars_status_insert_status vars x status ofs len substatus :
  wf_vars_status vars status ->
  wf_vars_status vars substatus ->
  Sv.Subset (read_e ofs) vars ->
  Sv.Subset (read_e len) vars ->
  wf_vars_status vars (insert_status x status ofs len substatus).
Proof.
  move=> status_vars substatus_vars ofs_vars len_vars.
  rewrite /insert_status.
  case: ifP => _ //.
  case: ifP => _.
  + by apply wf_vars_status_fill_status.
  apply wf_vars_status_clear_status => //.
  rewrite /wf_vars_zone /= /read_slice /=.
  by clear -ofs_vars len_vars; SvD.fsetdec.
Qed.

Lemma get_sub_statusP vme status s cs off :
  get_sub_status status s ->
  wf_status vme status ->
  sem_slice vme s = ok cs ->
  offset_in_concrete_slice cs off ->
  valid_offset vme status off.
Proof.
  move=> + + ok_cs off_in_cs.
  case: status => //= i hget [ci ok_ci].
  rewrite /valid_offset_interval ok_ci => _ [<-].
  elim: i hget ci ok_ci => [|s' i ih] /=.
  + by move=> _ _ [<-] /=.
  case: eqP => _ //.
  case hle1: (odflt _ _).
  + move=> hget.
    t_xrbindP=> _ cs' ok_cs' ci ok_ci <-.
    move=> /= /orP [off_in_cs'|off_in_ci].
    + have hdisj := symbolic_slice_ble_disjoint hle1 ok_cs ok_cs'.
      by apply (disjoint_concrete_sliceP hdisj off_in_cs off_in_cs').
    by apply (ih hget ci ok_ci off_in_ci).
  case hle2: (odflt _ _) => //.
  move=> hget.
  t_xrbindP=> _ cs' ok_cs' ci ok_ci <-.
  move=> /= /orP [off_in_cs'|off_in_ci].
  + have hdisj := symbolic_slice_ble_disjoint hle2 ok_cs' ok_cs.
    by apply (disjoint_concrete_sliceP hdisj off_in_cs' off_in_cs).
  by apply (ih hget ci ok_ci off_in_ci).
Qed.

Lemma valid_offset_insert_status_between vme status substatus ofs ofsi len leni x off :
  wf_status vme status ->
  wf_status vme substatus ->
  sem_sexpr vme ofs >>= to_int = ok ofsi ->
  sem_sexpr vme len >>= to_int = ok leni ->
  ofsi <= off < ofsi + leni ->
  valid_offset vme (insert_status x status ofs len substatus) off ->
  valid_offset vme substatus (off - ofsi).
Proof.
  move=> hwfs hwfs' ok_ofsi ok_leni hoff.
  rewrite /insert_status.
  case: andP => [|_].
  + move=> [/eqP ? _]; subst ofs.
    move: ok_ofsi => /= [<-].
    by rewrite Z.sub_0_r.
  case: ifP => [|_].
  + (* substatus is valid between 0 and len thanks to get_sub_status.
       We don't need the hyp about fill_status, we drop it. *)
    move=> hstatus _.
    have hslice:
      sem_slice vme {| ss_ofs := Sconst 0; ss_len := len |} = ok {| cs_ofs := 0%Z; cs_len := leni |}.
    + by rewrite /sem_slice /= ok_leni /=.
    apply (get_sub_statusP hstatus hwfs' hslice).
    rewrite /offset_in_concrete_slice /= !zify.
    by lia.
  (* We clear the status between 0 and len. So the valid_offset hyp is
     contradictory with hoff. *)
  move=> off_valid.
  have hzone:
    sem_zone vme [:: {| ss_ofs := ofs; ss_len := len |}] = ok {| cs_ofs := ofsi; cs_len := leni |}.
  + by rewrite /= /sem_slice /= ok_ofsi ok_leni /=.
  have [_ []] := valid_offset_clear_status hwfs hzone off_valid.
  by rewrite /offset_in_concrete_slice /= !zify.
Qed.

Lemma valid_offset_insert_status_disjoint vme status substatus ofs ofsi len leni x off :
  wf_status vme status ->
  sem_sexpr vme ofs >>= to_int = ok ofsi ->
  sem_sexpr vme len >>= to_int = ok leni ->
  0 <= off /\ off < size_slot x ->
  ~ ofsi <= off < ofsi + leni ->
  valid_offset vme (insert_status x status ofs len substatus) off ->
  valid_offset vme status off.
Proof.
  move=> hwfs ok_ofsi ok_leni hoff hnoff.
  rewrite /insert_status.
  case: andP => [|_].
  + move=> [/eqP ? /eqP ?]; subst ofs len.
    move: ok_ofsi ok_leni => /= [?] [?]; subst ofsi leni.
    by lia.
  have hslice:
    sem_slice vme {| ss_ofs := ofs; ss_len := len |} = ok {| cs_ofs := ofsi; cs_len := leni |}.
  + by rewrite /sem_slice /= ok_ofsi ok_leni /=.
  case: ifP => _.
  + (* off is outside the slice added by fill_status *)
    move=> off_valid.
    apply (valid_offset_fill_status hwfs hslice off_valid).
    by rewrite /offset_in_concrete_slice /= !zify.
  move=> off_valid.
  have hzone:
    sem_zone vme [:: {| ss_ofs := ofs; ss_len := len |}] = ok {| cs_ofs := ofsi; cs_len := leni |}.
  + by rewrite /= hslice.
  by case: (valid_offset_clear_status hwfs hzone off_valid).
Qed.

Lemma sub_region_status_at_ofs_addr vme sr ty ofs ofsi ty2 x status :
  wf_sub_region vme sr ty ->
  sem_sexpr vme ofs >>= to_int = ok ofsi ->
  0 <= ofsi /\ ofsi + size_of ty2 <= size_of ty ->
  sub_region_addr vme (sub_region_status_at_ofs x sr status ofs (Sconst (size_of ty2))).1 =
    sub_region_addr vme (sub_region_at_ofs sr ofs (Sconst (size_of ty2))).
Proof.
  move=> hwf ok_ofsi hofsi.
  rewrite /sub_region_status_at_ofs.
  case: andP => [|//] /=.
  move=> [/eqP ofs_0 _].
  have [addr haddr] := wf_sub_region_sub_region_addr hwf.
  rewrite (sub_region_addr_offset hwf ok_ofsi hofsi haddr).
  move: ok_ofsi; rewrite ofs_0 /= => -[<-].
  by rewrite wrepr0 GRing.addr0.
Qed.

(* TODO: move? *)
Lemma mk_ofs_int_vars aa ws e :
  Sv.Subset (read_e (mk_ofs_int aa ws e)) (read_e e).
Proof.
  rewrite /mk_ofs_int.
  case: is_const => [z|].
  + rewrite {1}/read_e /=.
    by clear; SvD.fsetdec.
  by rewrite /read_e /= -/read_e.
Qed.

(* Note that we assume [eq_sub_region_val_read] only on the (sub-)sub-region
   [(sub_region_status_at_ofs x srx statusx ofs len').1].
   We do not need it for the full sub-region [srx], since we can derive it for
   the rest of [srx] from the [valid_state] hypothesis. *)
Lemma valid_state_set_move_sub table rmap vme m0 s1 s2 (x:var_i) srx pk substatus e' e aa ws len v s1' :
  valid_state table rmap vme m0 s1 s2 ->
  Mvar.get rmap.(var_region) x = Some srx ->
  get_local pmap x = Some pk ->
  wf_status vme substatus ->
  wf_vars_status table.(vars) substatus ->
  Sv.Subset (read_e e') table.(vars) ->
  sem_sexpr vme e' >>= to_int = sem_pexpr true gd s1 e >>= to_int ->
  write_lval true gd (Lasub aa ws len x e) v s1 = ok s1' ->
  let ofs := mk_ofs_int aa ws e' in
  let len' := Sconst (arr_size ws len) in
  let statusx := get_var_status rmap srx.(sr_region) x in
  eq_sub_region_val_read vme s2.(emem) (sub_region_status_at_ofs x srx statusx ofs len').1 substatus v ->
  valid_state (remove_binding table x)
    (set_move_sub rmap srx.(sr_region) x statusx ofs len' substatus)
    vme m0 s1' s2.
Proof.
  move=> hvs hsrx hlx hwfs' substatus_vars vars_e' heq_int hwrite ofs len' statusx hread.
  have /wfr_wf hwfx := hsrx.
  have hwfsx: wf_status vme statusx.
  + by apply wfr_status.
  move: hwrite => /=.
  apply: on_arr_varP;
    t_xrbindP=> nx ax htyx hgetx i vi ok_vi ok_i av /to_arrI ? ax' ok_ax'
      /write_varP [-> hdb htr]; subst v.
  move: heq_int; rewrite ok_vi /= ok_i => ok_i'.
  have ok_ofsi: sem_sexpr vme ofs >>= to_int = ok (i * mk_scale aa ws).
  + by rewrite (mk_ofs_intP aa ws ok_i').
  have ok_leni: sem_sexpr vme len' >>= to_int = ok (arr_size ws len).
  + by [].
  case:(hvs) => hscs hvalid hdisj hincl hincl2 hunch hrip hrsp heqvm hwft hwfr heqmem hglobv htop.
  constructor => //=.
  + move=> y hgety; rewrite Vm.setP_neq; first by apply heqvm.
    by apply/eqP; rewrite /get_local in hlx; congruence.
  + by apply wf_table_set_var.
  case: (hwfr) => hwfsr hwfst hvarsz hvarss hval hptr; split=> //.
  + move=> ry y /=.
    rewrite get_var_status_set_move_status.
    case: eqP => //= _.
    case: eqP => //= _.
    by apply (wf_status_insert_status x hwfsx hwfs' ok_ofsi ok_leni).
  + move=> ry y /=.
    rewrite get_var_status_set_move_status.
    case: eqP => //= _.
    case: eqP => //= _.
    apply wf_vars_status_insert_status => //.
    + by apply hvarss.
    + rewrite /ofs.
      have := @mk_ofs_int_vars aa ws e'.
      move: vars_e'.
      by clear; SvD.fsetdec.
    rewrite /read_e /=.
    by clear; SvD.fsetdec.
  + move=> y sry statusy vy /=.
    move=> /(check_gvalid_set_move_sub hsrx) [].
    + move=> [hnglob heq -> ->].
      rewrite heq get_gvar_eq // -heq //= htyx eq_refl => -[<-].
      split=> // off addr w haddr off_valid /[dup] /get_val_byte_bound /= hb.
      rewrite (WArray.set_sub_get8 ok_ax') /=.
      case: ifPn; rewrite !zify => hoff.
      + have ->:
          (addr + wrepr Uptr off =
            addr + wrepr _ (i * mk_scale aa ws) + wrepr _ (off - i * mk_scale aa ws))%R.
        + by rewrite wrepr_sub -GRing.addrA (GRing.addrC (wrepr _ _)) GRing.subrK.
        apply hread.
        + have ->: len' = Sconst (size_of (sarr (Z.to_pos (arr_size ws len)))).
          + by rewrite /= Z2Pos.id //.
          have hbound: 
            0 <= i * mk_scale aa ws /\ i * mk_scale aa ws + size_of (sarr (Z.to_pos (arr_size ws len))) <= size_slot x.
          + rewrite htyx /= Z2Pos.id //.
            by apply (WArray.set_sub_bound ok_ax').
          rewrite (sub_region_status_at_ofs_addr _ _ hwfx ok_ofsi hbound).
          by apply (sub_region_addr_offset hwfx ok_ofsi hbound haddr).
        apply: (valid_offset_insert_status_between hwfsx hwfs' ok_ofsi ok_leni _ off_valid).
        by lia.
      have hgvalidx := check_gvalid_lvar hsrx.
      have /wfr_val -/(_ _ hgetx) [{}hread _] := hgvalidx.
      apply hread => //.
      apply: (valid_offset_insert_status_disjoint hwfsx ok_ofsi ok_leni _ _ off_valid).
      + by rewrite htyx /=.
      by lia.
    by move=> [? hgvalid]; rewrite get_gvar_neq => //; apply hval.
  move=> y sry /=.
  move=> /hptr [pky [hly hpky]].
  exists pky; split=> //.
  case: pky hly hpky => //=.
  move=> s ofs' ws' cs f hly heq.
  rewrite /check_stack_ptr get_var_status_set_move_status.
  case: eqP => // _; case: eqP => //=.
  have /wf_vnew := hlx.
  by have /wf_locals /wfs_new := hly; congruence.
Qed.

(* ------------------------------------------------------------------ *)

Definition mov_ofs_correct (mov_ofs : lval → assgn_tag → mov_kind → pexpr → pexpr → option instr_r) :=
  forall (P' : sprog) ev s1 e w ofs pofs x tag mk ins s2,
    p_globs P' = [::]
    -> sem_pexpr true [::] s1 e >>= to_pointer = ok w
    -> sem_pexpr true [::] s1 ofs >>= to_pointer = ok pofs
    -> mov_ofs x tag mk e ofs = Some ins
    -> write_lval true [::] x (Vword (w + pofs)) s1 = ok s2
    -> exists2 vm2, sem_i P' ev s1 ins (with_vm s2 vm2) & evm s2 =1 vm2.

Definition immediate_correct (immediate : var_i → Z → instr_r) :=
  forall (P' : sprog) w s (x: var_i) z,
    vtype x = sword Uptr ->
    sem_i P' w s (immediate x z)
      (with_vm s (evm s).[x <- Vword (wrepr Uptr z)]).

Definition swap_correct (swap : assgn_tag → var_i → var_i → var_i → var_i → instr_r) :=
  forall (P' : sprog) rip s tag (x y z w : var_i) (pz pw: pointer),
    vtype x = spointer -> vtype y = spointer -> 
    vtype z = spointer -> vtype w = spointer -> 
    (evm s).[z] = Vword pz ->
    (evm s).[w] = Vword pw -> 
    sem_i P' rip s (swap tag x y z w)
      (with_vm s ((evm s).[x <- Vword pw]).[y <- Vword pz]).

Record h_stack_alloc_params (saparams : stack_alloc_params) :=
  {
    (* [mov_ofs] must behave as described in stack_alloc.v. *)
    mov_ofsP : mov_ofs_correct saparams.(sap_mov_ofs);
    (* specification of sap_immediate *)
    sap_immediateP : immediate_correct saparams.(sap_immediate);
    sap_swapP : swap_correct saparams.(sap_swap)
  }.

Context
  (shparams : slh_lowering.sh_params)
  (hshparams : slh_lowering_proof.h_sh_params shparams)
  (saparams : stack_alloc_params)
  (hsaparams : h_stack_alloc_params saparams).

(* ------------------------------------------------------------------ *)

Lemma valid_state_vm_eq s2 vm2 table rmap vme mem s1 :
  (evm s2 =1 vm2)%vm ->
  valid_state table rmap vme mem s1 s2 ->
  valid_state table rmap vme mem s1 (with_vm s2 vm2).
Proof.
  move=> heq [hscs hsl hdisj hincl hincl' hunch hrip hrsp heqvm hwft hwfr heqsource hbetw htop].
  constructor => //=.
  1,2: by rewrite -heq.
  + by move=> ???; rewrite -heq; apply heqvm.
  case: hwfr => hwfsr hwfst hvarsz hvarss hV hP; constructor => //.
  move=> x sr /hP [pk [hgl hv]]; exists pk; split => //.
  by case: (pk) hv => //= >; rewrite heq.
Qed.

(* TODO: move? *)
Context
  (fresh_var_ident : v_kind -> PrimInt63.int -> string -> stype -> Ident.ident)
  (pp_sr : sub_region -> pp_error).

Local Lemma clone_ty : forall x n, vtype (clone fresh_var_ident x n) = vtype x.
Proof. by []. Qed.

Lemma sub_region_status_at_ofs_wf vme sr ty ofs ofsi ty2 x status sr' status' :
  wf_sub_region vme sr ty ->
  sem_sexpr vme ofs >>= to_int = ok ofsi ->
  0 <= ofsi /\ ofsi + size_of ty2 <= size_of ty ->
  sub_region_status_at_ofs x sr status ofs (Sconst (size_of ty2)) = (sr', status') ->
  wf_sub_region vme sr' ty2.
Proof.
  move=> hwf ok_ofsi hofsi.
  rewrite /sub_region_status_at_ofs.
  case: andP => [|_] /=.
  + move=> [_ /eqP heq] [<- _].
    apply: wf_sub_region_size_of hwf.
    by lia.
  move=> [<- _].
  by apply (sub_region_at_ofs_wf hwf ok_ofsi hofsi).
Qed.

Lemma sub_region_status_at_ofs_wf_status vme status x sr ofs len sr' status' :
  wf_status vme status ->
  sub_region_status_at_ofs x sr status ofs len = (sr', status') ->
  wf_status vme status'.
Proof.
  move=> hwfs.
  rewrite /sub_region_status_at_ofs.
  case: andP => _.
  + by move=> [_ <-].
  move=> [_ <-].
  by case: ifP => _.
Qed.

Lemma sub_region_status_at_ofs_wf_vars_zone vars x sr status ofs len sr' status' :
  wf_vars_zone vars sr.(sr_zone) ->
  Sv.Subset (read_e ofs) vars ->
  Sv.Subset (read_e len) vars ->
  sub_region_status_at_ofs x sr status ofs len = (sr', status') ->
  wf_vars_zone vars sr'.(sr_zone).
Proof.
  move=> sr_vars ofs_vars len_vars.
  rewrite /sub_region_status_at_ofs.
  case: ifP => _.
  + by move=> [<- _].
  move=> [<- _] /=.
  by apply sub_zone_at_ofs_wf_vars_zone.
Qed.

Lemma sub_region_status_at_ofs_wf_vars_status vars x sr status ofs len sr' status' :
  wf_vars_status vars status ->
  sub_region_status_at_ofs x sr status ofs len = (sr', status') ->
  wf_vars_status vars status'.
Proof.
  move=> status_vars.
  rewrite /sub_region_status_at_ofs.
  case: ifP => _.
  + by move=> [_ <-].
  move=> [_ <-] /=.
  by case: ifP.
Qed.

Lemma valid_offset_sub_region_status_at_ofs vme ofs ofsi len leni x sr status sr' status' off :
  wf_status vme status ->
  sem_sexpr vme ofs >>= to_int = ok ofsi ->
  sem_sexpr vme len >>= to_int = ok leni ->
  0 <= off < leni ->
  sub_region_status_at_ofs x sr status ofs len = (sr', status') ->
  valid_offset vme status' off ->
  valid_offset vme status (ofsi + off).
Proof.
  move=> hwfs ok_ofsi ok_leni hoff.
  rewrite /sub_region_status_at_ofs.
  case: andP => [|_].
  + move=> [/eqP ? _] [_ <-]; subst ofs.
    by move: ok_ofsi => /= -[<-].
  move=> [_ <-].
  case: ifP => // hget _.
  have ok_cs:
    sem_slice vme {| ss_ofs := ofs; ss_len := len |} = ok {| cs_ofs := ofsi; cs_len := leni |}.
  + by rewrite /sem_slice ok_ofsi ok_leni /=.
  apply (get_sub_statusP hget hwfs ok_cs).
  rewrite /offset_in_concrete_slice /= !zify.
  by lia.
Qed.

Lemma get_symbolic_of_pexprP table e table' e' :
  get_symbolic_of_pexpr (clone fresh_var_ident) table e = ok (table', e') ->
  symbolic_of_pexpr (clone fresh_var_ident) table e = ok (Some (table', e')).
Proof.
  rewrite /get_symbolic_of_pexpr.
  by t_xrbindP=> _ -> /o2rP ->.
Qed.

Lemma alloc_array_moveP vme m0 s1 s2 s1' table1 rmap1 table2 rmap2 r tag e v v' n i2 :
  valid_state table1 rmap1 vme m0 s1 s2 ->
  sem_pexpr true gd s1 e = ok v ->
  truncate_val (sarr n) v = ok v' ->
  write_lval true gd r v' s1 = ok s1' ->
  alloc_array_move saparams fresh_var_ident pp_sr pmap table1 rmap1 r tag e = ok (table2, rmap2, i2) →
  ∃ (s2' : estate) (vme' : Vm.t), [/\
    sem_i P' rip s2 i2 s2',
    valid_state (remove_binding_lval table2 r) rmap2 vme' m0 s1' s2' &
    vme =[table1.(vars)] vme'].
Proof.
  move=> hvs he /truncate_val_typeE[] a ?? hw; subst v v'.
  rewrite /alloc_array_move.
  t_xrbindP=> -[[[[[table1' sry] statusy] mk] ey] ofsy] He.

  have: exists vme' wey wofsy, [/\
    vme =[table1.(vars)] vme',
    Sv.Subset table1.(vars) table1'.(vars),
    wf_table table1' vme' s1.(evm),
    wf_sub_region vme' sry (sarr n),
    wf_status vme' statusy,
    wf_vars_zone table1'.(vars) (sr_zone sry),
    wf_vars_status table1'.(vars) statusy,
    sem_pexpr true [::] s2 ey >>= to_pointer = ok wey,
    sem_pexpr true [::] s2 ofsy >>= to_pointer = ok wofsy &
    sub_region_addr vme' sry = ok (wey + wofsy)%R /\
    eq_sub_region_val (sarr n) vme' (emem s2) sry statusy (Varr a)].
  + case: e he He => //=.
    + t_xrbindP=> y hgety vpky hkindy.
      case: vpky hkindy => [vpky|//] hkindy.
      t_xrbindP=> -[sry' statusy'] /(get_gsub_region_statusP hkindy) hgvalidy.
      assert (hwfy := check_gvalid_wf wfr_wf hgvalidy).
      have hwfpky := get_var_kind_wf hkindy.
      have /wfr_gptr := hgvalidy.
      rewrite hkindy => -[_ [[<-] hpky]].
      t_xrbindP=> -[ey' ofsy'] haddr <- <- <- _ <- <-.
      have [wey ok_wey haddry] :=
        addr_from_vpk_pexprP true hvs hwfpky hpky hwfy haddr.
      exists vme, wey, (wrepr Uptr ofsy'); split=> //.
      + by apply hvs.(vs_wf_table).
      + by rewrite -(type_of_get_gvar_array hgety).
      + by apply (check_gvalid_wf_status wfr_status hgvalidy).
      + by apply (check_gvalid_wf_vars_zone wfr_vars_zone hgvalidy).
      + by apply (check_gvalid_wf_vars_status wfr_vars_status hgvalidy).
      + by rewrite /= truncate_word_u.
      split=> //.
      assert (hval := wfr_val hgvalidy hgety).
      by rewrite -(type_of_get_gvar_array hgety).
    move=> aa ws len y e.
    apply: on_arr_gvarP => ny ay hyty hgety.
    apply: rbindP=> i ok_i.
    apply: rbindP=> a' ok_a /ok_inj /Varr_inj [?]; subst n => /= ?; subst a.
    t_xrbindP=> vpky hkindy.
    case: vpky hkindy => [vpky|//] hkindy.
    t_xrbindP=> -[sry' statusy'] /(get_gsub_region_statusP hkindy) hgvalidy.
    t_xrbindP=> -[table1'' e1] /get_symbolic_of_pexprP hsym.
    case hsub: sub_region_status_at_ofs => [sry'' statusy''].
    t_xrbindP=> -[ey' ofsy'] haddr e' halloc <- <- <- _ <- <- /=.
    move: ok_i; t_xrbindP=> vi ok_vi ok_i.
    have [vme' [hwft vme_eq hsem]] :=
      wf_table_symbolic_of_pexpr clone_ty hsym ok_vi hvs.(vs_wf_table).
    have hsubset := symbolic_of_pexpr_subset_vars hsym hvs.(vs_wf_table).(wft_vars).
    have hsubset' := symbolic_of_pexpr_subset_read hsym hvs.(vs_wf_table).(wft_vars).
    have {}hvs := valid_state_eq_on vme_eq hsubset hwft hvs.
    have /= hwfy := [elaborate check_gvalid_wf wfr_wf hgvalidy].
    have /= hwfsy := [elaborate check_gvalid_wf_status wfr_status hgvalidy].
    have hwfpky := get_var_kind_wf hkindy.
    have /wfr_gptr := hgvalidy.
    rewrite hkindy => -[_ [[<-] hpky]].
    have [wey ok_wey haddry] :=
      addr_from_vpk_pexprP true hvs hwfpky hpky hwfy haddr.
    have ok_i': sem_pexpr true [::] s2 e' >>= to_int = ok i.
    + have htr: truncate_val sint vi = ok (Vint i).
      + by rewrite /truncate_val /= ok_i /=.
      have [vi' [-> +]] := alloc_eP hvs halloc ok_vi htr.
      by rewrite /truncate_val /=; t_xrbindP=> i' -> <-.
    have ok_i'': sem_sexpr vme' e1 >>= to_int = ok i.
    + have [vi1 ok_vi1 incl_vi1] := hsem.
      have /= ok_i'' := of_value_uincl_te (ty:=sint) incl_vi1 ok_i.
      by rewrite ok_vi1 /= ok_i''.
    have hint:
      sem_sexpr vme' (mk_ofs_int aa ws e1) >>= to_int = ok (i * mk_scale aa ws).
    + by rewrite (mk_ofs_intP aa ws ok_i'').
    have hbound:
      0 <= i * mk_scale aa ws /\ i * mk_scale aa ws + size_of (sarr (Z.to_pos (arr_size ws len))) <= size_slot y.(gv).
    + rewrite hyty /= Z2Pos.id //.
      by apply (WArray.get_sub_bound ok_a).
    have haddry': sub_region_addr vme' sry'' = ok (wey + wrepr Uptr (i * mk_scale aa ws + ofsy'))%R.
    + have := sub_region_addr_offset hwfy hint hbound haddry.
      rewrite -(sub_region_status_at_ofs_addr y.(gv) statusy' hwfy hint hbound) /= Z2Pos.id // hsub.
      by rewrite -GRing.addrA -wrepr_add Z.add_comm.
    exists vme', wey, (wrepr Uptr (i * mk_scale aa ws + ofsy')); split=> //.
    + move: hsub; rewrite -{1}(Z2Pos.id (arr_size ws len)) // => hsub.
      by apply (sub_region_status_at_ofs_wf hwfy hint hbound hsub).
    + by apply (sub_region_status_at_ofs_wf_status hwfsy hsub).
    + apply: sub_region_status_at_ofs_wf_vars_zone hsub.
      + by apply (check_gvalid_wf_vars_zone wfr_vars_zone hgvalidy).
      + have := @mk_ofs_int_vars aa ws e1.
        by clear -hsubset'; SvD.fsetdec.
      rewrite /read_e /=.
      by clear; SvD.fsetdec.
    + apply: sub_region_status_at_ofs_wf_vars_status hsub.
      by apply (check_gvalid_wf_vars_status wfr_vars_status hgvalidy).
    + by rewrite (mk_ofsP aa ws ofsy' ok_i') /= truncate_word_u.
    split=> //.
    split=> // off addr w.
    rewrite haddry' => -[<-] off_valid ok_w.
    rewrite Z.add_comm wrepr_add GRing.addrA -(GRing.addrA (_ + _)%R _) -wrepr_add.
    have /wfr_val -/(_ _ hgety) [hread _] := hgvalidy.
    apply (hread _ _ _ haddry).
    + apply: (valid_offset_sub_region_status_at_ofs (leni:=arr_size ws len)
        hwfsy hint _ _ hsub off_valid) => //.
      have /get_val_byte_bound := ok_w.
      by rewrite /= Z2Pos.id.
    move: ok_w; rewrite /= (WArray.get_sub_get8 ok_a) /=.
    by case: ifP.

  move=> [vme' [wey [wofsy [vme_eq hsubset hwft hwfy hwfsy hvarszy hvarssy ok_wey ok_wofsy [haddry heqvaly]]]]].

  have {}hvs := valid_state_eq_on vme_eq hsubset hwft hvs.

  case: r hw => //.
  + move=> x /write_varP [ -> hdb h].
    have /vm_truncate_valE [hty htreq]:= h.
    case hlx: (get_local pmap x) => [pk|//].
    have /wf_locals hlocal := hlx.
    rewrite -hty in hwfy.
    rewrite -hty -htreq in heqvaly.

    case: pk hlx hlocal.
    + t_xrbindP=> s ofs' ws z sc hlx hlocal /eqP heqsub <- <- <-.
      exists s2, vme'; split=> //; first by constructor.
      (* valid_state update *)
      by apply (valid_state_set_move hvs hwfy hwfsy hvarszy hvarssy hlx heqsub h heqvaly).

    + move=> p hlx hlocal.
      rewrite /get_addr.
      case Hmov_ofs: (sap_mov_ofs saparams) => [ins| //].
      move=> /= [<- <- <-].
      have /(_ (with_vm s2 (evm s2).[p <- Vword (wey + wofsy)])) []:=
        mov_ofsP hsaparams rip P'_globs ok_wey ok_wofsy Hmov_ofs.
      + by rewrite /= write_var_eq_type //= hlocal.(wfr_rtype).
      move=> /= vm2 hsem heq1.
      exists (with_vm s2 vm2), vme'; split => //.
      (* valid_state update *)
      apply (@valid_state_vm_eq (with_vm s2 (evm s2).[p <- Vword (wey + wofsy)]) vm2) => //.
      by apply (valid_state_set_move_regptr hvs hwfy haddry hwfsy hvarszy hvarssy hlx h heqvaly).

    move=> s ofs' ws z f hlx hlocal hi2 /=.
    case: ifP hi2.
    + rewrite /is_nop.
      case heq: Mvar.get => [srx|//] /andP [/eqP ? hcheck] [<- <- <-]; subst srx.
      (* interestingly, hcheck is not needed for the proof *)
      exists s2, vme'; split=> //; first by constructor.
      apply: (valid_state_set_move hvs hwfy hwfsy hvarszy hvarssy hlx _ h heqvaly).
      move=> /= hcheck' paddr addry hpaddr haddry'.
      by have /wfr_ptr := heq; rewrite hlx => -[_ [[<-] hpk]]; apply hpk.
    move=> _.
    rewrite /get_addr.
    case Hmov_ofs: (sap_mov_ofs saparams) => [ins| //].
    move=> /= [<- <- <-].
    have hwf := sub_region_stkptr_wf vme' hlocal.
    have [paddr hpaddr] := wf_sub_region_sub_region_addr hwf.
    have hvp: validw (emem s2) Aligned paddr Uptr.
    + have hofs: 0 <= 0 /\ wsize_size Uptr <= size_of (sword Uptr) by move=> /=; lia.
      have := validw_sub_region_addr_ofs hvs hwf hpaddr hofs.
      rewrite wrepr0 GRing.addr0; apply.
      by apply (is_align_sub_region_stkptr hlocal hpaddr).
    have /writeV -/(_ (wey + wofsy)%R) [mem2 hmem2] := hvp.
    have /(_ (with_mem s2 mem2)) []:=
      mov_ofsP hsaparams rip P'_globs ok_wey ok_wofsy Hmov_ofs.
    + rewrite /= /get_var vs_rsp /= !truncate_word_u /=.
      move: hpaddr; rewrite (sub_region_addr_stkptr _ hlocal) => -[->].
      by rewrite hmem2.
    move=> vm2 hsem heq1.
    exists (with_vm (with_mem s2 mem2) vm2), vme'; split => //.
    apply valid_state_vm_eq => //.
    apply: (valid_state_set_stack_ptr hvs hwfy haddry hwfsy hvarszy hvarssy hlx hpaddr _ _ _ _ h heqvaly).
    + by apply (Memory.write_mem_stable hmem2).
    + by move=> ??; apply (write_validw_eq hmem2).
    + by move=> ??? /disjoint_range_alt; apply (writeP_neq _ hmem2).
    by rewrite (writeP_eq hmem2).

  (* interestingly, we can prove that n = Z.to_pos len = Z.to_pos (arr_size ws len2)
     but it does not seem useful
  *)
  move=> aa ws len2 x e' hw.
  case hlx: (get_local pmap x) => [pk|//].
  t_xrbindP=> -[srx statusx] /get_sub_region_statusP [hsrx ->].
  t_xrbindP=> -[table1'' e1] /get_symbolic_of_pexprP hsym.
  case hsub: sub_region_status_at_ofs => [srx' statusx'].
  t_xrbindP=> /eqP ? <- <- <-; subst srx'.
  have []: exists i, sem_pexpr true gd s1 e' >>= to_int = ok i.
  + move: hw; rewrite /write_lval.
    apply: on_arr_varP; t_xrbindP=> ?????? -> /= -> _ _ _ _ _.
    by eexists; reflexivity.
  t_xrbindP=> i ve' ok_ve' ok_i.
  have [vme'' [hwft'' vme_eq' hsem]] :=
    wf_table_symbolic_of_pexpr clone_ty hsym ok_ve' hwft.
  exists s2, vme''; split=> /=; first by constructor.
  + have hsubset' := symbolic_of_pexpr_subset_vars hsym hwft.(wft_vars).
    have {}hvs := valid_state_eq_on vme_eq' hsubset' hwft'' hvs.
    have heq_int:
      sem_sexpr vme'' e1 >>= to_int = sem_pexpr true gd s1 e' >>= to_int.
    + have [ve1 ok_ve1 huincl] := hsem.
      rewrite ok_ve1 ok_ve' /= ok_i.
      by apply (of_value_uincl_te (ty:=sint) huincl ok_i).
    have heqvaly': eq_sub_region_val (sarr n) vme'' (emem s2) sry statusy (Varr a).
    + by apply (eq_sub_region_val_eq_on vme_eq' hvarszy hvarssy).
    apply: (valid_state_set_move_sub hvs hsrx hlx _ _ _ heq_int hw).
    + by apply: (wf_status_eq_on vme_eq' hvarssy).
    + by apply (subset_vars_wf_vars_status hsubset' hvarssy).
    + have := symbolic_of_pexpr_subset_read hsym hwft.(wft_vars).
      by clear -hsubset'; SvD.fsetdec.
    rewrite hsub.
    by case: heqvaly' => [hread _].
  apply (eq_onT vme_eq).
  by apply (eq_onI hsubset vme_eq').
Qed.

Lemma is_protect_ptr_failP rs o es r e msf :
  is_protect_ptr_fail rs o es = Some(r, e, msf) ->
  [/\ exists sz, o = Oslh (SLHprotect_ptr_fail sz),
      rs = [:: r] &
      es = [:: e; msf]].
Proof.
  case: o rs es => //= -[] // sz [ | r' []] // [ | e' [ | msf' []]] // [-> -> ->].
  by split => //; exists sz.
Qed.

Lemma wfr_VARS_ZONE_alloc_protect_ptr rmap1 ii r tag e msf rmap2 i2 vars :
  alloc_protect_ptr shparams pmap rmap1 ii r tag e msf = ok (rmap2, i2) ->
  wfr_VARS_ZONE vars rmap1 ->
  wfr_VARS_ZONE vars rmap2.
Proof.
  rewrite /alloc_protect_ptr.
  t_xrbindP=> -[[sry statusy] ?] He + hvarsz1.

  have sry_vars: wf_vars_zone vars sry.(sr_zone).
  + case: e He => //=.
    t_xrbindP=> y vpky hkindy.
    case: vpky hkindy => [vpky|//] hkindy.
    t_xrbindP=> _ [sry' statusy'] /(get_gsub_region_statusP hkindy) hgvalidy.
    t_xrbindP=> -[_ _] _ [<- _ _].
    by apply (check_gvalid_wf_vars_zone hvarsz1 hgvalidy).

  case: r => // x.
  case: get_local => [pk|//].
  case: pk => //.
  t_xrbindP=> _ _ _ _ _ <- _.
  by apply wfr_VARS_ZONE_set_move.
Qed.

Lemma wfr_VARS_STATUS_alloc_protect_ptr rmap1 ii r tag e msf rmap2 i2 vars :
  alloc_protect_ptr shparams pmap rmap1 ii r tag e msf = ok (rmap2, i2) ->
  wfr_VARS_STATUS vars rmap1 ->
  wfr_VARS_STATUS vars rmap2.
Proof.
  rewrite /alloc_protect_ptr.
  t_xrbindP=> -[[sry statusy] ?] He + hvarss1.

  have statusy_vars: wf_vars_status vars statusy.
  + case: e He => //=.
    t_xrbindP=> y vpky hkindy.
    case: vpky hkindy => [vpky|//] hkindy.
    t_xrbindP=> _ [sry' statusy'] /(get_gsub_region_statusP hkindy) hgvalidy.
    t_xrbindP=> -[_ _] _ [_ <- _].
    by apply (check_gvalid_wf_vars_status hvarss1 hgvalidy).

  case: r => // x.
  case: get_local => [pk|//].
  case: pk => //.
  t_xrbindP=> _ _ _ _ _ <- _.
  by apply wfr_VARS_STATUS_set_move_status.
Qed.

(* The proof mostly consists in copied parts of alloc_array_moveP. *)
Lemma alloc_protect_ptrP table vme m0 s1 s2 s1' rmap1 rmap2 ii r tag e msf vmsf v v' n i2 :
  valid_state table rmap1 vme m0 s1 s2 ->
  sem_pexpr true gd s1 e = ok v ->
  sem_pexpr true gd s1 msf = ok vmsf ->
  truncate_val ty_msf vmsf = ok (@Vword msf_size 0%R) ->
  truncate_val (sarr n) v = ok v' ->
  write_lval true gd r v' s1 = ok s1' ->
  alloc_protect_ptr shparams pmap rmap1 ii r tag e msf = ok (rmap2, i2) ->
  ∃ s2' : estate, sem_i P' rip s2 i2 s2' ∧ valid_state (remove_binding_lval table r) rmap2 vme m0 s1' s2'.
Proof.
  move=> hvs he hmsf htr; rewrite /truncate_val /=.
  t_xrbindP=> a /to_arrI ? ? hw; subst v v'.
  rewrite /alloc_protect_ptr.
  t_xrbindP=> -[[sry statusy] ey] He.

  have: exists wey, [/\
    wf_sub_region vme sry (sarr n),
    wf_status vme statusy,
    wf_vars_zone table.(vars) sry.(sr_zone),
    wf_vars_status table.(vars) statusy,
    sem_pexpr true [::] s2 ey >>= to_pointer = ok wey,
    sub_region_addr vme sry = ok wey &
    eq_sub_region_val (sarr n) vme (emem s2) sry statusy (Varr a)].
  + case: e he He => //=.
    t_xrbindP=> y hgety vpky hkindy.
    case: vpky hkindy => [vpky|//] hkindy.
    t_xrbindP=> hvpky -[sry' statusy'] /(get_gsub_region_statusP hkindy) hgvalidy.
    assert (hwfy := check_gvalid_wf wfr_wf hgvalidy).
    have hwfpky := get_var_kind_wf hkindy.
    have /wfr_gptr := hgvalidy.
    rewrite hkindy => -[_ [[<-] hpky]].
    t_xrbindP=> -[ey' ofsy'] haddr [<- <- <-].
    have [wey ok_wey haddry] :=
      addr_from_vpk_pexprP true hvs hwfpky hpky hwfy haddr. 
    exists wey; split=> //.
    + by rewrite -(type_of_get_gvar_array hgety).
    + by apply (check_gvalid_wf_status wfr_status hgvalidy).
    + by apply (check_gvalid_wf_vars_zone wfr_vars_zone hgvalidy).
    + by apply (check_gvalid_wf_vars_status wfr_vars_status hgvalidy).
    + move: haddry.
      have ->: ofsy' = 0.
      + by case: (vpky) hvpky haddr => // -[] //= ? _ [] _ <-.
      by rewrite wrepr0 GRing.addr0.
    assert (hval := wfr_val hgvalidy hgety).
    by rewrite -(type_of_get_gvar_array hgety).

  move=> [wey [hwfy hwfsy hvarszy hvarssy ok_wey haddry heqvaly]].

  case: r hw => //.
  move=> x /write_varP [-> hdb h].
  have /vm_truncate_valE [hty htreq]:= h.
  case hlx: (get_local pmap x) => [pk|//].
  have /wf_locals hlocal := hlx.
  rewrite -hty in hwfy.
  rewrite -hty -htreq in heqvaly.

  case: pk hlx hlocal => //.
  move=> p hlx hlocal.
  t_xrbindP=> msf' hmsf' i hi <- <-.
  exists (with_vm s2 s2.(evm).[p <- Vword wey]); split; last first.
  + by apply (valid_state_set_move_regptr hvs hwfy haddry hwfsy hvarszy hvarssy hlx h heqvaly).
  move: hi; rewrite /lower_protect_ptr_fail /slh_lowering.lower_slho /=.
  case heq: slh_lowering.shp_lower => [ [[xs o] es] | //] [<-].

  move: ok_wey; t_xrbindP=> vey ok_vey ok_wey.
  have [vmsf' [ok_vmsf' htr']] := alloc_eP hvs hmsf' hmsf htr.
  have hto: to_word msf_size vmsf' = ok 0%R.
  + by move: htr'; rewrite /truncate_val /=; t_xrbindP=> _ -> ->.
  constructor; rewrite /= P'_globs.
  apply
    (slh_lowering_proof.hshp_spec_lower hshparams
      (args := [:: vey; vmsf']) (res := [:: Vword wey]) heq).
  + by eexists; first by reflexivity.
  + by rewrite /= ok_vey ok_vmsf' /=.
  + by rewrite /exec_sopn /= ok_wey hto /=.
  rewrite /= write_var_truncate //.
  apply subtype_truncatable.
  rewrite /= hlocal.(wfr_rtype).
  by apply subtype_refl.
Qed.

Lemma is_swap_arrayP o : 
  reflect (exists n,  o = Opseudo_op (pseudo_operator.Oswap (sarr n))) (is_swap_array o).
Proof.
  case: o => /=; try by constructor => -[].
  case => /=; try by constructor => -[].
  move=> s; case: is_sarrP => h; constructor.
  + by case: h => n ->; eauto.
  move=> [n []] heq; apply h; eauto.
Qed.

Lemma get_regptrP x p :
  get_regptr pmap x = ok p ->
  Mvar.get pmap.(locals) x = Some (Pregptr p).
Proof. by rewrite /get_regptr; case heq: get_local => [[]|] // [<-]. Qed.

Lemma wfr_VARS_ZONE_alloc_array_swap rmap1 xs tag es rmap2 i2 vars :
  alloc_array_swap saparams pmap rmap1 xs tag es = ok (rmap2, i2) ->
  wfr_VARS_ZONE vars rmap1 ->
  wfr_VARS_ZONE vars rmap2.
Proof.
  rewrite /alloc_array_swap.
  case: xs => // -[] // x [] // [] // y [] //.
  case: es => // -[] // z [] // [] // w [] //=.
  t_xrbindP=> ?? -[srz _] /get_sub_region_statusP [hsrz ->].
  t_xrbindP=> ?? -[srw _] /get_sub_region_statusP [hsrw ->].
  t_xrbindP=> ?? ?? _ <- _.
  move=> hvarsz1.
  apply wfr_VARS_ZONE_set_move.
  + by apply (hvarsz1 _ _ hsrz).
  apply wfr_VARS_ZONE_set_move => //.
  by apply (hvarsz1 _ _ hsrw).
Qed.

Lemma wfr_VARS_STATUS_alloc_array_swap rmap1 xs tag es rmap2 i2 vars :
  alloc_array_swap saparams pmap rmap1 xs tag es = ok (rmap2, i2) ->
  wfr_VARS_STATUS vars rmap1 ->
  wfr_VARS_STATUS vars rmap2.
Proof.
  rewrite /alloc_array_swap.
  case: xs => // -[] // x [] // [] // y [] //.
  case: es => // -[] // z [] // [] // w [] //=.
  t_xrbindP=> ?? -[srz _] /get_sub_region_statusP [hsrz ->].
  t_xrbindP=> ?? -[srw _] /get_sub_region_statusP [hsrw ->].
  t_xrbindP=> ?? ?? _ <- _.
  move=> hvarss1.
  apply wfr_VARS_STATUS_set_move_status => //.
  by apply wfr_VARS_STATUS_set_move_status.
Qed.

Lemma alloc_array_swapP table m0 vme s1 s2 s1' rmap1 rmap2 n xs tag es va vs i2:
  valid_state table rmap1 vme m0 s1 s2 ->
  sem_pexprs true gd s1 es = ok va -> 
  exec_sopn (Opseudo_op (pseudo_operator.Oswap (sarr n))) va = ok vs -> 
  write_lvals true gd s1 xs vs = ok s1' -> 
  alloc_array_swap saparams pmap rmap1 xs tag es = ok (rmap2, i2) ->
  ∃ s2' : estate, sem_i P' rip s2 i2 s2' ∧ valid_state (foldl remove_binding_lval table xs) rmap2 vme m0 s1' s2'.
Proof.
  move=> hvs.
  rewrite /alloc_array_swap.
  case: xs => // -[] // x [] // [] // y [] //.
  case: es => // -[] // z [] // [] // w [] //=.
  t_xrbindP => vz hz _ vw hw <- <-.
  rewrite /exec_sopn /= /sopn_sem /sopn_sem_ /= /swap_semi; t_xrbindP.
  move=> _ tz /to_arrI hvz tw /to_arrI hvw <- <- /=; t_xrbindP; subst vz vw.
  move=> _ /write_varP [-> _ /[dup] hxtr /vm_truncate_valE [hxty hxtr']].
  move=> _ /write_varP [-> _ /[dup] hytr /vm_truncate_valE [hyty hytr']].
  rewrite with_vm_idem /= => ?; subst s1'.
  move=> pz /get_regptrP hpz [srz _] /get_sub_region_statusP [hsrz ->].
  t_xrbindP.
  move=> pw /get_regptrP hpw [srw _] /get_sub_region_statusP [hsrw ->].
  t_xrbindP.
  move=> px /get_regptrP hpx py /get_regptrP hpy /andP [xloc yloc] <- <-.

  have hzty := type_of_get_gvar_array hz.
  have /wfr_wf hwfz := hsrz.
  have [addrz ok_addrz] := wf_sub_region_sub_region_addr hwfz.
  have := check_gvalid_lvar hsrz;
    (rewrite mk_lvar_nglob; last by apply /negP; rewrite -is_lvar_is_glob) => hgvalidz.
  have hwfsz := [elaborate check_gvalid_wf_status wfr_status hgvalidz].
  have hvarszz := [elaborate check_gvalid_wf_vars_zone wfr_vars_zone hgvalidz].
  have hvarssz := [elaborate check_gvalid_wf_vars_status wfr_vars_status hgvalidz].
  have /wfr_ptr := hsrz; rewrite /get_local hpz => -[_ [[<-] /= hpkz]].
  assert (heqvalz := wfr_val hgvalidz hz).
  rewrite hzty -hyty in hwfz.
  rewrite hzty -hyty -hytr' in heqvalz.

  have hwty := type_of_get_gvar_array hw.
  have /wfr_wf hwfw := hsrw.
  have [addrw ok_addrw] := wf_sub_region_sub_region_addr hwfw.
  have := check_gvalid_lvar hsrw;
    (rewrite mk_lvar_nglob; last by apply /negP; rewrite -is_lvar_is_glob) => hgvalidw.
  have hwfsw := [elaborate check_gvalid_wf_status wfr_status hgvalidw].
  have hvarszw := [elaborate check_gvalid_wf_vars_zone wfr_vars_zone hgvalidw].
  have hvarssw := [elaborate check_gvalid_wf_vars_status wfr_vars_status hgvalidw].
  have /wfr_ptr := hsrw; rewrite /get_local hpw => -[_ [[<-] /= hpkw]].
  assert (heqvalw := wfr_val hgvalidw hw).
  rewrite hwty -hxty in hwfw.
  rewrite hwty -hxty -hxtr' in heqvalw.

  set s2' := with_vm s2 (evm s2).[px <- Vword addrw].
  set s2'' := with_vm s2' (evm s2').[py <- Vword addrz].
  exists s2''; split.
  + apply: hsaparams.(sap_swapP).
    + by apply: (wf_locals hpx).(wfr_rtype).
    + by apply: (wf_locals hpy).(wfr_rtype).
    + by apply: (wf_locals hpz).(wfr_rtype).
    + by apply: (wf_locals hpw).(wfr_rtype).
    + by apply (hpkz _ ok_addrz).
    by apply (hpkw _ ok_addrw).
  have hvs' := valid_state_set_move_regptr hvs hwfw ok_addrw hwfsw hvarszw hvarssw hpx hxtr heqvalw.
  by apply: (valid_state_set_move_regptr hvs' hwfz ok_addrz hwfsz hvarszz hvarssz hpy hytr heqvalz).
Qed.

Lemma alloc_array_move_initP vme m0 s1 s2 s1' table1 table2 rmap1 rmap2 r tag e v v' n i2 :
  valid_state table1 rmap1 vme m0 s1 s2 ->
  sem_pexpr true gd s1 e = ok v ->
  truncate_val (sarr n) v = ok v' ->
  write_lval true gd r v' s1 = ok s1' ->
  alloc_array_move_init saparams fresh_var_ident pp_sr pmap table1 rmap1 r tag e = ok (table2, rmap2, i2) →
  ∃ (s2' : estate) vme', [/\
    sem_i P' rip s2 i2 s2',
    valid_state (remove_binding_lval table2 r) rmap2 vme' m0 s1' s2' &
    vme =[table1.(vars)] vme'].
Proof.
  move=> hvs.
  rewrite /alloc_array_move_init.
  case: is_array_initP; last first.
  + by move=> _; apply alloc_array_moveP.
  move=> [m ->] /= [<-].
  rewrite /truncate_val /=.
  t_xrbindP=> _ /WArray.cast_empty_ok -> {m} <-.
  case: r => //=.
  t_xrbindP=> x /write_varP [-> _ htr] srx /get_sub_regionP hsrx <- <- <-.
  exists s2, vme; split=> //; first by constructor.
  (* valid_state update *)
  have /wfr_wf hwfx := hsrx.
  have /wfr_ptr [pkx [hlx hpkx]] := hsrx.
  have hgvalidx := check_gvalid_lvar hsrx.
  have /= hwfsx := [elaborate check_gvalid_wf_status wfr_status hgvalidx].
  apply: (valid_state_set_move hvs hwfx _ _ _ hlx hpkx htr) => //.
  + by apply (wfr_vars_zone hsrx).
  have /vm_truncate_valE [-> ->] := htr.
  split=> //= off addr w _ _ /=.
  by rewrite WArray.get_empty; case: ifP.
Qed.

(* Link between a reg ptr argument value [va] in the source and
   the corresponding pointer [p] in the target. [m1] is the source memory,
   [m2] is the target memory.
*)
(* TODO: We use va (arg in the source) only to know the size of the argument.
   Would it make sense to use the type instead? Is there a benefit? *)
Record wf_arg_pointer m1 m2 (wptrs:seq (option bool)) vargs vargs' (writable:bool) align va p i := {
  wap_align             : is_align p align;
    (* [p] is aligned *)
  wap_no_overflow       : no_overflow p (size_val va);
    (* [p + size_val va - 1] does not overflow *)
  wap_valid             : forall w, between p (size_val va) w U8 -> validw m2 Aligned w U8;
    (* the bytes in [p ; p + size_val va - 1] are valid *)
    wap_fresh             : forall w, validw m1 Aligned w U8 -> disjoint_zrange p (size_val va) w (wsize_size U8);
    (* the bytes in [p ; p + size_val va - 1] are disjoint from the valid bytes of [m1] *)
  wap_writable_not_glob : writable -> (0 < glob_size)%Z -> disjoint_zrange rip glob_size p (size_val va);
    (* if the reg ptr is marked as writable, the associated zone in the target
       memory is disjoint from the globals *)
  wap_writable_disjoint : writable ->
    forall j vaj pj, i <> j ->
      isSome (nth None wptrs j) ->
      nth (Vbool true) vargs j = vaj ->
      nth (Vbool true) vargs' j = @Vword Uptr pj ->
      disjoint_zrange p (size_val va) pj (size_val vaj)
    (* if the reg ptr is marked as writable, the associated zone in the target
       memory is disjoint from all the zones pointed to by other reg ptr *)
}.

(* Link between the values given as arguments in the source and the target. *)
Definition wf_arg m1 m2 (wptrs:seq (option bool)) aligns vargs vargs' i :=
  match nth None wptrs i with
  | None => True
  | Some writable =>
    exists p,
      nth (Vbool true) vargs' i = Vword p /\
      wf_arg_pointer m1 m2 wptrs vargs vargs' writable (nth U8 aligns i) (nth (Vbool true) vargs i) p i
  end.

Definition wf_args m1 m2 (wptrs:seq (option bool)) aligns vargs vargs' :=
  forall i, wf_arg m1 m2 wptrs aligns vargs vargs' i.

Definition value_in_mem m v v' :=
  exists p, v' = Vword p /\
    forall off w, get_val_byte v off = ok w -> read m Aligned (p + wrepr _ off)%R U8 = ok w.

Definition value_eq_or_in_mem {A} m (o:option A) v v' :=
  match o with
  | None => v' = v (* no reg ptr : both values are equal *)
  | Some _ => (* reg ptr : [va] is compiled to a pointer [p] that satisfies [wf_arg_pointer] *)
    value_in_mem m v v'
  end.

(* Link between a reg ptr result value [vr1] in the source and the corresponding
   value [vr2] in the target. The reg ptr is associated to
   the [i]-th elements of [vargs1] and [vargs2] (the arguments in the source and
   the target).
*)
Record wf_result_pointer vargs1 vargs2 i vr1 vr2 := {
  wrp_subtype : subtype (type_of_val vr1) (type_of_val (nth (Vbool true) vargs1 i));
    (* [vr1] is smaller than the value taken as an argument (in the source) *)
    (* actually, size_of_val vr1 <= size_of_val (nth (Vbool true) vargs1 i) is enough to do the proofs,
       but this is true and we have lemmas about [subtype] (e.g. [wf_sub_region_subtype] *)
  wrp_args    : vr2 = nth (Vbool true) vargs2 i;
    (* [vr2] is the same pointer as the corresponding argument (in the target) *)
}.

(* Link between the values returned by the function in the source and the target. *)
Definition wf_result vargs1 vargs2 (i : option nat) vr1 vr2 :=
  match i with
  | None => True
  | Some i => wf_result_pointer vargs1 vargs2 i vr1 vr2
  end.

Lemma get_PvarP e x : get_Pvar e = ok x -> e = Pvar x.
Proof. by case: e => //= _ [->]. Qed.

Lemma alloc_call_arg_aux_not_None rmap0 rmap opi e rmap2 bsr e' :
  alloc_call_arg_aux pmap rmap0 rmap opi e = ok (rmap2, (bsr, e')) ->
  forall pi, opi = Some pi -> exists sr, bsr = Some (pi.(pp_writable), sr).
Proof.
  move=> halloc pi ?; subst opi.
  move: halloc; rewrite /alloc_call_arg_aux.
  t_xrbindP=> x _ _.
  case: get_local => [pk|//].
  case: pk => // p.
  t_xrbindP=> -[[sr ?] ?] _; t_xrbindP=> _ _ _ _ _ /= <- _.
  by eexists.
Qed.

Lemma alloc_call_args_aux_not_None rmap sao_params args rmap2 l :
  alloc_call_args_aux pmap rmap sao_params args = ok (rmap2, l) ->
  List.Forall2 (fun opi bsr => forall pi, opi = Some pi ->
    exists sr, bsr = Some (pi.(pp_writable), sr)) sao_params (map fst l).
Proof.
  rewrite /alloc_call_args_aux.
  elim: sao_params args {2}rmap rmap2 l.
  + move=> [|//] _ _ _ /= [_ <-]; constructor.
  move=> opi sao_params ih [//|arg args] rmap0 /=.
  t_xrbindP=> _ _ [rmap1 [bsr e]] halloc [rmap2 l] /= /ih{}ih _ <-.
  constructor=> //.
  by apply (alloc_call_arg_aux_not_None halloc).
Qed.

Lemma set_clearP rmap x sr rmap2 :
  set_clear rmap x sr = ok rmap2 ->
  sr.(sr_region).(r_writable) /\
  rmap2 = set_clear_pure rmap sr.
Proof. by rewrite /set_clear; t_xrbindP=> /check_writableP -> ->. Qed.

Lemma alloc_call_arg_aux_writable rmap0 rmap opi e rmap2 bsr e' :
  alloc_call_arg_aux pmap rmap0 rmap opi e = ok (rmap2, (bsr, e')) ->
  forall sr, bsr = Some (true, sr) ->
  sr.(sr_region).(r_writable).
Proof.
  move=> halloc sr ?; subst bsr.
  move: halloc; rewrite /alloc_call_arg_aux.
  t_xrbindP=> x _ _.
  case: opi => [pi|].
  + case: get_local => [pk|//].
    case: pk => // p.
    t_xrbindP=> -[[sr' ?] ?] /= _; t_xrbindP=> _ _ tt hclear _ hw <- _.
    by move: hclear; rewrite hw => /set_clearP [? _].
  case: get_local => //.
  by t_xrbindP.
Qed.

Lemma alloc_call_args_aux_writable rmap sao_params args rmap2 l :
  alloc_call_args_aux pmap rmap sao_params args = ok (rmap2, l) ->
  List.Forall (fun bsr => forall sr, bsr = Some (true, sr) ->
    sr.(sr_region).(r_writable)) (map fst l).
Proof.
  rewrite /alloc_call_args_aux.
  elim: sao_params args {2}rmap rmap2 l.
  + by move=> [|//] _ _ _ [_ <-]; constructor.
  move=> opi sao_params ih [//|arg args] rmap0 /=.
  t_xrbindP=> _ _ [rmap1 [bsr e]] halloc [rmap2 l] /= /ih{}ih _ <-.
  constructor=> //.
  by apply (alloc_call_arg_aux_writable halloc).
Qed.

Lemma incl_status_refl : Reflexive incl_status.
Proof.
  move=> status.
  case: status => //= i.
  by apply incl_interval_refl.
Qed.

Lemma incl_status_map_refl : Reflexive incl_status_map.
Proof.
  move=> sm.
  apply Mvar.inclP => x.
  case: Mvar.get => [status|//].
  by apply incl_status_refl.
Qed.

Lemma incl_refl : Reflexive incl.
Proof.
  move=> rmap.
  apply /andP; split.
  + apply Mvar.inclP => x.
    by case: Mvar.get => [sr|//].
  apply Mr.inclP => r.
  case: Mr.get => [sm|//].
  by apply incl_status_map_refl.
Qed.

Lemma incl_status_trans : Transitive incl_status.
Proof.
  case=> [||i1] [||i2] [||i3] //= hincl1 hincl2.
  by apply (incl_interval_trans hincl2 hincl1).
Qed.

Lemma incl_status_map_trans : Transitive incl_status_map.
Proof.
  move=> sm1 sm2 sm3.
  move=> /Mvar.inclP h1 /Mvar.inclP h2.
  apply Mvar.inclP => x.
  case heq1: Mvar.get => [status1|//].
  have := h1 x; rewrite heq1.
  case heq2: Mvar.get => [status2|//] hincl.
  have := h2 x; rewrite heq2.
  case heq3: Mvar.get => [status3|//].
  by apply (incl_status_trans hincl).
Qed.

Lemma incl_trans : Transitive incl.
Proof.
  move=> rmap1 rmap2 rmap3.
  move=> /andP [] /Mvar.inclP h12 /Mr.inclP h12'.
  move=> /andP [] /Mvar.inclP h23 /Mr.inclP h23'.
  apply /andP; split.
  + apply Mvar.inclP => x.
    case heq1: Mvar.get => [sr1|//].
    have := h12 x; rewrite heq1.
    case heq2: Mvar.get => [sr2|//] /eqP ?; subst sr2.
    by have := h23 x; rewrite heq2.
  apply Mr.inclP => r.
  case heq1: Mr.get => [sm1|//].
  have := h12' r; rewrite heq1.
  case heq2: Mr.get => [sm2|//] hincl.
  have := h23' r; rewrite heq2.
  case heq3: Mr.get => [sm3|//].
  by apply (incl_status_map_trans hincl).
Qed.

Lemma get_var_status_None rv r x :
  Mr.get rv r = None ->
  get_var_status rv r x = Unknown.
Proof.
  move=> hget.
  rewrite /get_var_status /get_status_map hget /=.
  by rewrite /get_status /empty_status_map Mvar.get0.
Qed.

(* This is not exactly the Prop-version of [incl]. [incl] has the disadvantage
   that a map with dummy bindings (e.g. associating empty bytes to a var) is not
   [incl] in the map without the dummy bindings, while equivalent from the point
   of view of the definitions that we care about ([get_var_bytes],
   [check_valid], [valid_state]). [Incl] avoids this pitfall.
*)
Definition Incl (rmap1 rmap2 : region_map) :=
  (forall x sr, Mvar.get rmap1.(var_region) x = Some sr -> Mvar.get rmap2.(var_region) x = Some sr) /\
  (forall r x, incl_status (get_var_status rmap1 r x) (get_var_status rmap2 r x)).

Lemma Incl_refl : Reflexive Incl.
Proof.
  move=> rmap.
  split=> //.
  by move=> r x; apply incl_status_refl.
Qed.

Lemma Incl_trans : Transitive Incl.
Proof.
  move=> rmap1 rmap2 rmap3.
  move=> [hincl11 hincl12] [hincl21 hincl22]; split.
  + by move=> x sr /hincl11 /hincl21.
  by move=> r x; apply (incl_status_trans (hincl12 r x) (hincl22 r x)).
Qed.

Lemma Incl_check_gvalid rmap1 rmap2 x sr status :
  Incl rmap1 rmap2 ->
  check_gvalid rmap1 x = Some (sr, status) ->
  exists2 status2,
    check_gvalid rmap2 x = Some (sr, status2) &
    incl_status status status2.
Proof.
  move=> [hincl1 hincl2].
  rewrite /check_gvalid.
  case: is_glob.
  + move=> ->.
    exists status => //.
    by apply incl_status_refl.
  case heq1: Mvar.get=> [sr'|//] [? <-]; subst sr'.
  rewrite (hincl1 _ _ heq1).
  eexists; first by reflexivity.
  by apply hincl2.
Qed.

Lemma incl_var_region rmap1 rmap2 x sr :
  incl rmap1 rmap2 ->
  Mvar.get rmap1.(var_region) x = Some sr ->
  Mvar.get rmap2.(var_region) x = Some sr.
Proof.
  move=> /andP [hincl _] hget1.
  have /Mvar.inclP -/(_ x) := hincl.
  rewrite hget1.
  by case: Mvar.get => // _ /eqP <-.
Qed.

Lemma incl_get_var_status rmap1 rmap2 r x :
  incl rmap1 rmap2 ->
  incl_status (get_var_status rmap1 r x) (get_var_status rmap2 r x).
Proof.
  move=> /andP [] _ /Mr.inclP /(_ r).
  rewrite /get_var_status /get_status_map /get_status.
  case: Mr.get => [sm1|//].
  case: Mr.get => [sm2|//].
  move=> /Mvar.inclP /(_ x).
  case: Mvar.get => [status1|//].
  by case: Mvar.get => [status2|//].
Qed.

Lemma incl_check_gvalid rmap1 rmap2 x sr status :
  incl rmap1 rmap2 ->
  check_gvalid rmap1 x = Some (sr, status) ->
  exists2 status2,
    check_gvalid rmap2 x = Some (sr, status2) &
    incl_status status status2.
Proof.
  move=> hincl.
  rewrite /check_gvalid.
  case: is_glob.
  + move=> ->.
    exists status => //.
    by apply incl_status_refl.
  case heq1: Mvar.get=> [sr'|//] [? <-]; subst sr'.
  rewrite (incl_var_region hincl heq1).
  eexists; first by reflexivity.
  by apply: incl_get_var_status hincl.
Qed.

Lemma incl_statusP status1 status2 vme off :
  incl_status status1 status2 ->
  wf_status vme status1 ->
  valid_offset vme status1 off ->
  valid_offset vme status2 off.
Proof.
  case: status1 status2 => [||i1] [||i2] //=.
  by apply incl_intervalP.
Qed.

Lemma wf_rmap_incl vars rmap1 rmap2 vme s1 s2 :
  incl rmap1 rmap2 ->
  wfr_STATUS rmap1 vme ->
  wfr_VARS_STATUS vars rmap1 ->
  wf_rmap vars rmap2 vme s1 s2 ->
  wf_rmap vars rmap1 vme s1 s2.
Proof.
  move=> hincl hwfst1 hvarss1 hwfr2.
  case: (hwfr2) => hwfsr2 hwfst2 hvarsz2 hvarss2 hval2 hptr2; split=> //.
  + move=> x sr1 /(incl_var_region hincl).
    by apply hwfsr2.
  + move=> x sr1 /(incl_var_region hincl).
    by apply hvarsz2.
  + move=> x sr1 status1 v hgvalid1 hget.
    have [status2 hgvalid2 {}hincl] := incl_check_gvalid hincl hgvalid1.
    have [hread2 hty2] := hval2 _ _ _ _ hgvalid2 hget.
    split=> //.
    move=> off addr w haddr off_valid.
    apply hread2 => //.
    have /= hwfs1 := check_gvalid_wf_status hwfst1 hgvalid1.
    by apply (incl_statusP hincl hwfs1 off_valid).
  move=> x sr1 /(incl_var_region hincl) /hptr2 [pk [hlx hpk2]].
  exists pk; split=> //.
  case: pk hlx hpk2 => //= sl ofs ws cs f hlx hpk hstkptr.
  apply hpk.
  have := incl_get_var_status (sub_region_stkptr sl ws cs).(sr_region) f hincl.
  move: hstkptr; rewrite /check_stack_ptr.
  move=> /is_validP ->.
  by case: get_var_status.
Qed.

Lemma valid_state_incl rmap1 rmap2 vme table m0 s s' :
  incl rmap1 rmap2 ->
  wfr_STATUS rmap1 vme ->
  wfr_VARS_STATUS table.(vars) rmap1 ->
  valid_state table rmap2 vme m0 s s' ->
  valid_state table rmap1 vme m0 s s'.
Proof.
  move=> hincl hwfst hvarss hvs.
  case:(hvs) => hscs hvalid hdisj hincl' hincl2 hunch hrip hrsp heqvm hwft' hwfr heqmem hglobv htop.
  constructor=> //.
  by apply (wf_rmap_incl hincl hwfst hvarss hwfr).
Qed.

Lemma incl_Incl rmap1 rmap2 : incl rmap1 rmap2 -> Incl rmap1 rmap2.
Proof.
  move=> hincl; split.
  + by move=> x sr; apply (incl_var_region hincl).
  by move=> r x; apply (incl_get_var_status _ _ hincl).
Qed.

Lemma wf_rmap_Incl vars1 vars2 rmap1 rmap2 vme s1 s2 :
  Incl rmap2 rmap1 ->
  wfr_STATUS rmap2 vme ->
  wfr_VARS_ZONE vars2 rmap2 ->
  wfr_VARS_STATUS vars2 rmap2 ->
  wf_rmap vars1 rmap1 vme s1 s2 ->
  wf_rmap vars2 rmap2 vme s1 s2.
Proof.
  move=> /[dup] hincl [hinclr hincls] hwfst2 hvarsz2 hvarss2 hwfr1.
  case: (hwfr1) => hwfsr1 hwfst1 hvarsz1 hvarss1 hval1 hptr1; split=> //.
  + move=> x sr /hinclr.
    by apply hwfsr1.
  + move=> x sr status2 v hgvalid2 hget.
    have [status1 hgvalid1 {}hincl] := Incl_check_gvalid hincl hgvalid2.
    have [hread1 hty] := hval1 _ _ _ _ hgvalid1 hget.
    split=> //.
    move=> off addr w haddr off_valid.
    apply hread1 => //.
    have /= hwfs2 := check_gvalid_wf_status hwfst2 hgvalid2.
    by apply (incl_statusP hincl hwfs2 off_valid).
  move=> x sr /hinclr /hptr1 [pk [hlx hpk1]].
  exists pk; split=> //.
  case: pk hlx hpk1 => //= sl ofs ws cs f hlx hpk1 hstkptr.
  apply hpk1.
  have := hincls (sub_region_stkptr sl ws cs).(sr_region) f.
  move: hstkptr; rewrite /check_stack_ptr.
  move=> /is_validP ->.
  by case: get_var_status.
Qed.

Lemma valid_state_Incl_gen rmap1 rmap2 vme table1 table2 m0 s s' :
  wf_table table2 vme s.(evm) ->
  Incl rmap2 rmap1 ->
  wfr_STATUS rmap2 vme ->
  wfr_VARS_ZONE table2.(vars) rmap2 ->
  wfr_VARS_STATUS table2.(vars) rmap2 ->
  valid_state table1 rmap1 vme m0 s s' ->
  valid_state table2 rmap2 vme m0 s s'.
Proof.
  move=> hwft2 hincl hwfst2 hvarsz2 hvarss2 hvs1.
  case:(hvs1) => hscs hvalid hdisj hincl' hincl2 hunch hrip hrsp heqvm hwft' hwfr heqmem hglobv htop.
  constructor=> //.
  by apply (wf_rmap_Incl hincl hwfst2 hvarsz2 hvarss2 hwfr).
Qed.

(* simpler version with unchanged table *)
Lemma valid_state_Incl rmap1 rmap2 vme table m0 s s' :
  Incl rmap2 rmap1 ->
  wfr_STATUS rmap2 vme ->
  wfr_VARS_STATUS table.(vars) rmap2 ->
  valid_state table rmap1 vme m0 s s' ->
  valid_state table rmap2 vme m0 s s'.
Proof.
  move=> hincl hwfst2 hvarss2 hvs1.
  have hwft1 := hvs1.(vs_wf_table).
  have hvarsz1 := hvs1.(vs_wf_region).(wfr_vars_zone).
  apply: (valid_state_Incl_gen hwft1 hincl hwfst2 _ hvarss2 hvs1).
  have [hinclr _] := hincl.
  move=> x sr /hinclr.
  by apply hvarsz1.
Qed.

Lemma merge_interval_None i1 :
  foldl (fun acc s => let%opt acc := acc in add_sub_interval acc s) None i1 = None.
Proof. by elim: i1. Qed.

Lemma merge_interval_r i1 i2 i :
  merge_interval i1 i2 = Some i ->
  incl_interval i2 i.
Proof.
  rewrite /merge_interval.
  elim: i1 i2 i => [|s1 i1 ih1] i2 i /=.
  + by move=> [<-]; apply incl_interval_refl.
  case hadd: add_sub_interval => [i2'|]; last first.
  + by rewrite merge_interval_None.
  move=> /ih1.
  apply incl_interval_trans.
  by apply (add_sub_interval_incl_l hadd).
Qed.

Lemma merge_interval_l i1 i2 i :
  merge_interval i1 i2 = Some i ->
  incl_interval i1 i.
Proof.
  rewrite /merge_interval.
  elim: i1 i2 i => [//|s1 i1 ih1] i2 i /=.
  case hadd: add_sub_interval => [i2'|]; last first.
  + by rewrite merge_interval_None.
  move=> /[dup] /ih1 ->; rewrite andbT.
  move=> /merge_interval_r hincl.
  have := add_sub_interval_incl_r hadd; rewrite /= andbT.
  by apply /allP.
Qed.

Lemma incl_status_merge_status_l vars x status1 status2 status :
  merge_status vars x (Some status1) (Some status2) = Some status ->
  incl_status status status1.
Proof.
  move=> /=.
  case: status1 status2 => [||i1] [||i2] //=.
  + by move=> [<-].
  + by case: ifP => // _ [<-].
  + by case: ifP => // _ [<-] /=; apply incl_interval_refl.
  apply: obindP=> i hmerge.
  case: ifP => // _ [<-] /=.
  by apply (merge_interval_l hmerge).
Qed.

Lemma incl_status_merge_status_r vars x status1 status2 status :
  merge_status vars x (Some status1) (Some status2) = Some status ->
  incl_status status status2.
Proof.
  move=> /=.
  case: status1 status2 => [||i1] [||i2] //=.
  + by move=> [<-].
  + by case: ifP => // _ [<-] /=; apply incl_interval_refl.
  + by case: ifP => // _ [<-].
  apply: obindP=> i hmerge.
  case: ifP => // _ [<-] /=.
  by apply (merge_interval_r hmerge).
Qed.

Lemma incl_status_map_merge_status_l vars sm1 sm2 :
  incl_status_map (Mvar.map2 (merge_status vars) sm1 sm2) sm1.
Proof.
  apply Mvar.inclP => x.
  rewrite Mvar.map2P //.
  case hmerge: merge_status => [status|//].
  case: Mvar.get hmerge => [status1|//].
  case: Mvar.get => [status2|//].
  by apply incl_status_merge_status_l.
Qed.

Lemma incl_status_map_merge_status_r vars sm1 sm2 :
  incl_status_map (Mvar.map2 (merge_status vars) sm1 sm2) sm2.
Proof.
  apply Mvar.inclP => x.
  rewrite Mvar.map2P //.
  case hmerge: merge_status => [status|//].
  case: Mvar.get hmerge => [status1|//].
  case: Mvar.get => [status2|//].
  by apply incl_status_merge_status_r.
Qed.

Lemma incl_merge_l vars rmap1 rmap2 : incl (merge vars rmap1 rmap2) rmap1.
Proof.
  rewrite /merge; apply /andP => /=; split.
  + apply Mvar.inclP => x.
    rewrite Mvar.map2P //.
    case: Mvar.get => [sr1|//].
    case: Mvar.get => [sr2|//].
    by case: eqP.
  apply Mr.inclP => r.
  rewrite Mr.map2P //.
  rewrite /merge_status_map.
  case: Mr.get => [sm1|//].
  case: Mr.get => [sm2|//].
  case: Mvar.is_empty => //.
  by apply incl_status_map_merge_status_l.
Qed.

Lemma incl_merge_r vars rmap1 rmap2 : incl (merge vars rmap1 rmap2) rmap2.
Proof.
  rewrite /merge; apply /andP => /=; split.
  + apply Mvar.inclP => x.
    rewrite Mvar.map2P //.
    case: Mvar.get => [sr1|//].
    case: Mvar.get => [sr2|//].
    by case: ifP.
  apply Mr.inclP => r.
  rewrite Mr.map2P //.
  rewrite /merge_status_map.
  case: Mr.get => [sm1|//].
  case: Mr.get => [sm2|//].
  case: Mvar.is_empty => //.
  by apply incl_status_map_merge_status_r.
Qed.

Lemma incl_clear_status status z :
  incl_status (odflt Unknown (clear_status status z)) status.
Proof.
  case: z => [//|s z] /=.
  case: status => //= i.
  case hadd: add_sub_interval => [i2|//] /=.
  by apply (add_sub_interval_incl_l hadd).
Qed.

Lemma incl_clear_status_map_aux rmap z x status :
  incl_status (odflt Unknown (clear_status_map_aux rmap z x status)) status.
Proof.
  rewrite /clear_status_map_aux.
  case: (let%opt _ := _ in get_suffix _ _) => [[z1|]|//] /=;
    last by apply incl_status_refl.
  by apply incl_clear_status.
Qed.

Lemma incl_status_map_clear_status_map rmap z sm :
  incl_status_map (clear_status_map rmap z sm) sm.
Proof.
  apply /Mvar.inclP => x.
  rewrite /clear_status_map Mvar.filter_mapP.
  case: Mvar.get => [status|//] /=.
  have := incl_clear_status_map_aux rmap z x status.
  by case: clear_status_map_aux.
Qed.

(* If we used the optim "do not put empty status_map in the map", then I think
   we could remove the condition. *)
Lemma incl_set_clear_pure (rmap:region_map) sr :
  Mr.get rmap sr.(sr_region) <> None ->
  incl (set_clear_pure rmap sr) rmap.
Proof.
  move=> hnnone.
  apply /andP; split=> /=.
  + apply Mvar.inclP => x.
    by case: Mvar.get => [srx|//].
  apply /Mr.inclP => r.
  rewrite /set_clear_status Mr.setP.
  case: eqP => [<-|_].
  + rewrite /get_status_map.
    case heq: Mr.get hnnone => [sm|//] _ /=.
    by apply incl_status_map_clear_status_map.
  case: Mr.get => // bm.
  by apply incl_status_map_refl.
Qed.

Lemma get_var_status_set_clear_status rmap sr r y :
  get_var_status (set_clear_status rmap sr) r y =
    let statusy := get_var_status rmap r y in
    if sr.(sr_region) != r then statusy
    else
      odflt Unknown (clear_status_map_aux rmap sr.(sr_zone) y statusy).
Proof.
  rewrite /set_clear_status /get_var_status.
  rewrite get_status_map_setP.
  case: eqP => [->|//] /=.
  by apply get_status_clear.
Qed.

Lemma wfr_STATUS_set_clear_status rmap vme sr ty :
  wfr_WF rmap vme ->
  wf_sub_region vme sr ty ->
  wfr_STATUS rmap vme ->
  wfr_STATUS (set_clear_status rmap sr) vme.
Proof.
  move=> hwfsr hwf hwfst.
  move=> r y /=.
  rewrite get_var_status_set_clear_status.
  case: eq_op => //=.
  by apply: wf_status_clear_status_map_aux hwf.(wfsr_zone).
Qed.

Lemma wfr_VARS_STATUS_set_clear_status vars (rmap:region_map) sr :
  wfr_VARS_ZONE vars rmap ->
  wf_vars_zone vars sr.(sr_zone) ->
  wfr_VARS_STATUS vars rmap ->
  wfr_VARS_STATUS vars (set_clear_status rmap sr).
Proof.
  move=> hvarsz sr_vars hvarss.
  move=> r x.
  rewrite get_var_status_set_clear_status.
  case: eq_op => //=.
  by apply wf_vars_status_clear_status_map_aux.
Qed.

Lemma alloc_call_arg_aux_incl (rmap0 rmap:region_map) opi e rmap2 bsr e2 :
  (forall r, Mr.get rmap0 r <> None -> Mr.get rmap r <> None) ->
  alloc_call_arg_aux pmap rmap0 rmap opi e = ok (rmap2, (bsr, e2)) -> [/\
    incl rmap2 rmap,
    forall x sr,
      Mvar.get rmap.(var_region) x = Some sr ->
      Mvar.get rmap2.(var_region) x = Some sr &
    forall r, Mr.get rmap0 r <> None -> Mr.get rmap2 r <> None].
Proof.
  move=> hincl.
  rewrite /alloc_call_arg_aux.
  t_xrbindP=> x _ _.
  case: opi => [pi|].
  + case: get_local => [pk|//].
    case: pk => // p.
    t_xrbindP=> -[sr _] /get_sub_region_statusP [hsr ->].
    t_xrbindP=> /check_validP hstatus _ /= {}rmap2 hclear <- _ _.
    case: pp_writable hclear; last first.
    + move=> [<-]; split=> //.
      by apply incl_refl.
    move=> /set_clearP [hw ->].
    split=> //.
    + apply incl_set_clear_pure.
      apply hincl.
      move=> hnone.
      by move: hstatus; rewrite (get_var_status_None _ hnone).
    move=> r /=.
    rewrite /set_clear_status Mr.setP.
    case: eqP => [//|_].
    by apply hincl.
  case: get_local => [//|].
  t_xrbindP=> _ <- _ _.
  split=> //.
  by apply incl_refl.
Qed.

Lemma alloc_call_args_aux_incl_aux (rmap0 rmap:region_map) err sao_params args rmap2 l :
  (forall r, Mr.get rmap0 r <> None -> Mr.get rmap r <> None) ->
  fmapM2 err (alloc_call_arg_aux pmap rmap0) rmap sao_params args = ok (rmap2, l) ->
  incl rmap2 rmap /\
  (forall x sr, Mvar.get rmap.(var_region) x = Some sr -> Mvar.get rmap2.(var_region) x = Some sr).
Proof.
  elim: sao_params args rmap rmap2 l.
  + by move=> [|//] rmap _ _ _ [<- _]; split=> //; apply incl_refl.
  move=> opi sao_params ih [//|arg args] rmap /=.
  t_xrbindP=> _ _ hnnone [rmap1 [bsr e]] halloc [rmap2 l] /= /ih{}ih <- _.
  have [hincl hinclr hnnone2] := alloc_call_arg_aux_incl hnnone halloc.
  have [hincl2 hinclr2] := ih hnnone2.
  split.
  + by apply: (incl_trans hincl2 hincl).
  by move=> ?? /hinclr /hinclr2.
Qed.

Lemma alloc_call_args_aux_incl rmap sao_params args rmap2 l :
  alloc_call_args_aux pmap rmap sao_params args = ok (rmap2, l) ->
  incl rmap2 rmap.
Proof. by case/alloc_call_args_aux_incl_aux. Qed.

Lemma alloc_call_arg_aux_wfr_STATUS vme (rmap0 rmap:region_map) opi e rmap2 bsr e2 :
  wfr_WF rmap0 vme ->
  wfr_WF rmap vme ->
  wfr_STATUS rmap vme ->
  alloc_call_arg_aux pmap rmap0 rmap opi e = ok (rmap2, (bsr, e2)) ->
  wfr_WF rmap2 vme /\ wfr_STATUS rmap2 vme.
Proof.
  move=> hwfsr0 hwfsr hwfst.
  rewrite /alloc_call_arg_aux.
  t_xrbindP=> x _ _.
  case: opi => [pi|].
  + case: get_local => [pk|//].
    case: pk => // p.
    t_xrbindP=> -[sr _] /get_sub_region_statusP [hsr ->].
    t_xrbindP=> /check_validP hstatus _ /= {}rmap2 hclear <- _ _.
    case: pp_writable hclear; last first.
    + by move=> [<-]; split.
    move=> /set_clearP [hw ->].
    split=> //=.
    by apply (wfr_STATUS_set_clear_status hwfsr (hwfsr0 _ _ hsr) hwfst).
  case: get_local => [//|].
  by t_xrbindP=> _ <- _ _; split.
Qed.

Lemma alloc_call_args_aux_wfr_STATUS_aux vme (rmap0 rmap:region_map) err sao_params args rmap2 l :
  wfr_WF rmap0 vme ->
  wfr_WF rmap vme ->
  wfr_STATUS rmap vme ->
  fmapM2 err (alloc_call_arg_aux pmap rmap0) rmap sao_params args = ok (rmap2, l) ->
  wfr_STATUS rmap2 vme.
Proof.
  move=> hwfst0.
  elim: sao_params args rmap rmap2 l.
  + by move=> [|//] /= rmap _ _ _ hwfst [<- _].
  move=> opi sao_params ih [//|arg args] rmap /=.
  t_xrbindP=> _ _ hwfsr hwfst [rmap1 [bsr e]] halloc [rmap2 l] /= /ih{}ih <- _.
  have [hwfsr1 hwfst1] := alloc_call_arg_aux_wfr_STATUS hwfst0 hwfsr hwfst halloc.
  by apply ih.
Qed.

Lemma alloc_call_args_aux_wfr_STATUS vme rmap sao_params args rmap2 l :
  wfr_WF rmap vme ->
  wfr_STATUS rmap vme ->
  alloc_call_args_aux pmap rmap sao_params args = ok (rmap2, l) ->
  wfr_STATUS rmap2 vme.
Proof. by move=> /[dup]; apply alloc_call_args_aux_wfr_STATUS_aux. Qed.

Lemma wfr_VARS_ZONE_alloc_call_arg_aux rmap0 rmap opi e rmap2 bsr e2 vars :
  alloc_call_arg_aux pmap rmap0 rmap opi e = ok (rmap2, (bsr, e2)) ->
  wfr_VARS_ZONE vars rmap ->
  wfr_VARS_ZONE vars rmap2.
Proof.
  rewrite /alloc_call_arg_aux.
  t_xrbindP=> x _ _.
  case: opi => [pi|]; last first.
  + case: get_local => //.
    by t_xrbindP=> _ <- _ _.
  case: get_local => [pk|//].
  case: pk => // p.
  t_xrbindP=> -[sr _] /get_sub_region_statusP [hsr ->].
  t_xrbindP=> _ _ {}rmap2 hrmap2 <- _ _.
  case: ifP hrmap2 => _; last by move=> [<-].
  by move=> /set_clearP [_ ->].
Qed.

(* might probably be deduced from incl *)
Lemma wfr_VARS_ZONE_alloc_call_args_aux rmap sao_params args rmap2 l vars :
  alloc_call_args_aux pmap rmap sao_params args = ok (rmap2, l) ->
  wfr_VARS_ZONE vars rmap ->
  wfr_VARS_ZONE vars rmap2.
Proof.
  rewrite /alloc_call_args_aux.
  move: {1}rmap => rmap0.
  elim: sao_params args rmap rmap2 l => [|opi sao_params ih] [|arg args] //= rmap rmap2 l.
  + by move=> [<- _].
  t_xrbindP=> -[rmap' [??]] halloc [{}rmap2 ?] /= hallocs <- _.
  move=> hvarsz.
  have hvarsz' := wfr_VARS_ZONE_alloc_call_arg_aux halloc hvarsz.
  by apply: ih hallocs hvarsz'.
Qed.

Lemma alloc_call_arg_aux_wfr_VARS_ZONE_sub_region rmap0 rmap opi e rmap2 bsr e2 vars :
  alloc_call_arg_aux pmap rmap0 rmap opi e = ok (rmap2, (bsr, e2)) ->
  wfr_VARS_ZONE vars rmap0 ->
  forall b sr, bsr = Some (b, sr) -> wf_vars_zone vars sr.(sr_zone).
Proof.
  rewrite /alloc_call_arg_aux.
  t_xrbindP=> x _ _.
  case: opi => [pi|]; last first.
  + case: get_local => //.
    by t_xrbindP=> _ _ <- _.
  case: get_local => [pk|//].
  case: pk => // p.
  t_xrbindP=> -[sr _] /get_sub_region_statusP [hsr ->].
  t_xrbindP=> _ _ _ _ _ <- _.
  move=> hvarsz0 _ _ [_ <-].
  by apply (hvarsz0 _ _ hsr).
Qed.

Lemma alloc_call_args_aux_wfr_VARS_ZONE_sub_region rmap sao_params args rmap2 l vars :
  alloc_call_args_aux pmap rmap sao_params args = ok (rmap2, l) ->
  wfr_VARS_ZONE vars rmap ->
  List.Forall (fun bsr => forall b sr, bsr = Some (b, sr) -> wf_vars_zone vars sr.(sr_zone)) (map fst l).
Proof.
  move=> /[swap].
  rewrite /alloc_call_args_aux.
  move: {1 2}rmap => rmap0 hvarsz0.
  elim: sao_params args rmap rmap2 l => [|opi sao_params ih] [|arg args] //= rmap rmap2 l.
  + by move=> [_ <-].
  t_xrbindP=> -[rmap' [bsr ?]] halloc [{}rmap2 {}l] /= hallocs _ <- /=.
  constructor.
  + by apply (alloc_call_arg_aux_wfr_VARS_ZONE_sub_region halloc hvarsz0).
  by apply: ih hallocs.
Qed.

Lemma wfr_VARS_STATUS_alloc_call_arg_aux rmap0 rmap opi e rmap2 bsr e2 vars :
  alloc_call_arg_aux pmap rmap0 rmap opi e = ok (rmap2, (bsr, e2)) ->
  wfr_VARS_ZONE vars rmap0 ->
  wfr_VARS_ZONE vars rmap ->
  wfr_VARS_STATUS vars rmap ->
  wfr_VARS_STATUS vars rmap2.
Proof.
  rewrite /alloc_call_arg_aux.
  t_xrbindP=> x _ _.
  case: opi => [pi|]; last first.
  + case: get_local => //.
    by t_xrbindP=> _ <- _ _.
  case: get_local => [pk|//].
  case: pk => // p.
  t_xrbindP=> -[sr _] /get_sub_region_statusP [hsr ->].
  t_xrbindP=> _ _ {}rmap2 hrmap2 <- _ _.
  case: ifP hrmap2 => _; last by move=> [<-].
  move=> /set_clearP [_ ->] /=.
  move=> hvarsz0 hvarsz hvarss.
  apply wfr_VARS_STATUS_set_clear_status => //.
  by apply (hvarsz0 _ _ hsr).
Qed.

Lemma wfr_VARS_STATUS_alloc_call_args_aux rmap sao_params args rmap2 l vars :
  alloc_call_args_aux pmap rmap sao_params args = ok (rmap2, l) ->
  wfr_VARS_ZONE vars rmap ->
  wfr_VARS_STATUS vars rmap ->
  wfr_VARS_STATUS vars rmap2.
Proof.
  rewrite /alloc_call_args_aux => hallocs.
  move=> /[dup] hvarsz.
  move: {1 2}rmap hvarsz hallocs => rmap0 hvarsz0.
  elim: sao_params args rmap rmap2 l => [|opi sao_params ih] [|arg args] //= rmap rmap2 l.
  + by move=> [<- _].
  t_xrbindP=> -[rmap' [??]] halloc [{}rmap2 ?] /= hallocs <- _.
  move=> hvarsz hvarss.
  have hvarsz' := wfr_VARS_ZONE_alloc_call_arg_aux halloc hvarsz.
  have hvarss' := wfr_VARS_STATUS_alloc_call_arg_aux halloc hvarsz0 hvarsz hvarss.
  by apply: ih hallocs hvarsz' hvarss'.
Qed.

Lemma alloc_call_arg_aux_uincl table rmap0 rmap vme m0 s1 s2 opi e1 rmap2 bsr e2 wdb v1 :
  valid_state table rmap0 vme m0 s1 s2 ->
  alloc_call_arg_aux pmap rmap0 rmap opi e1 = ok (rmap2, (bsr, e2)) ->
  sem_pexpr wdb gd s1 e1 = ok v1 ->
  exists v2,
    sem_pexpr wdb [::] s2 e2 = ok v2 /\
    value_eq_or_in_mem (emem s2) opi v1 v2.
Proof.
  move=> hvs.
  rewrite /alloc_call_arg_aux.
  t_xrbindP=> x /get_PvarP ->.
  case: x => x [] //= _.
  case: opi => [pi|]; last first.
  + case hlx: get_local => //.
    t_xrbindP=> /check_diffP hnnew _ _ <- /= hget.
    have hkind: get_var_kind pmap (mk_lvar x) = ok None.
    + by rewrite /get_var_kind /= hlx.
    rewrite (get_var_kindP hvs hkind hnnew hget).
    by eexists; split; first by reflexivity.
  case hlx: get_local => [pk|//].
  case: pk hlx => // p hlx.
  t_xrbindP=> -[sr _] /get_sub_region_statusP [hsr ->].
  t_xrbindP=> /check_validP hvalid _ _ _ _ _ <- /= hget.
  have /wfr_wf hwf := hsr.
  have [addr ok_addr] := wf_sub_region_sub_region_addr hwf.
  have /wfr_ptr := hsr.
  rewrite hlx => -[_ [[<-] /=]] hgetp.
  rewrite get_gvar_nglob // /get_var /= (hgetp _ ok_addr) /= orbT /=.
  eexists; split; first by reflexivity.
  eexists; split; first by reflexivity.
  have hget' : get_gvar true gd (evm s1) {| gv := x; gs := Slocal |} = ok v1.
  + have /is_sarrP [len hty] := wfr_type (wf_pmap0.(wf_locals) hlx).
    move: hget; rewrite /get_gvar /= => /get_varP [].
    by rewrite /get_var hty => <- ? /compat_valEl [a] ->.
  have hgvalid := check_gvalid_lvar hsr.
  have /(wfr_val hgvalid) [hread /= hty] := hget'.
  move=> off w /[dup] /get_val_byte_bound; rewrite hty => hoff.
  apply: hread ok_addr _.
  by rewrite hvalid.
Qed.

Lemma alloc_call_args_aux_uincl table rmap vme m0 s1 s2 sao_params args rmap2 l wdb vargs1 :
  valid_state table rmap vme m0 s1 s2 ->
  alloc_call_args_aux pmap rmap sao_params args = ok (rmap2, l) ->
  sem_pexprs wdb gd s1 args = ok vargs1 ->
  exists vargs2,
    sem_pexprs wdb [::] s2 (map snd l) = ok vargs2 /\
    Forall3 (value_eq_or_in_mem (emem s2)) sao_params vargs1 vargs2.
Proof.
  move=> hvs.
  rewrite /alloc_call_args_aux.
  elim: sao_params args {2}rmap rmap2 l vargs1.
  + move=> [|//] /= _ _ _ l [_ <-] [<-] /=.
    eexists; split; first by reflexivity.
    by constructor.
  move=> opi sao_params ih [//|arg args] rmap0 /=.
  t_xrbindP=> _ _ _ [rmap1 [bsr e]] halloc [rmap2 l] /= /ih{}ih _ <-
    varg1 hvarg1 vargs1 hvargs1 <-.
  have [varg2 [hvarg2 heqinmem]] := alloc_call_arg_aux_uincl hvs halloc hvarg1.
  have [vargs2 [hvargs2 heqinmems]] := ih _ hvargs1.
  rewrite /= hvarg2 /= hvargs2 /=.
  eexists; split; first by reflexivity.
  by constructor.
Qed.

Lemma alloc_call_arg_aux_wf table rmap0 rmap vme m0 s1 s2 opi e1 rmap2 e2 wdb vargs vargs' wptrs aligns i :
  valid_state table rmap0 vme m0 s1 s2 ->
  alloc_call_arg_aux pmap rmap0 rmap opi e1 = ok (rmap2, e2) ->
  sem_pexpr wdb gd s1 e1 = ok (nth (Vbool true) vargs i) ->
  sem_pexpr wdb [::] s2 e2.2 = ok (nth (Vbool true) vargs' i) ->
  nth None wptrs i = omap pp_writable opi ->
  nth U8 aligns i = oapp pp_align U8 opi ->
  (nth None wptrs i = Some true ->
    forall j vai vaj (pi pj : word Uptr),
    i <> j ->
    isSome (nth None wptrs j) ->
    nth (Vbool true) vargs i = vai ->
    nth (Vbool true) vargs j = vaj ->
    nth (Vbool true) vargs' i = Vword pi ->
    nth (Vbool true) vargs' j = Vword pj ->
    disjoint_zrange pi (size_val vai) pj (size_val vaj)) ->
  wf_arg (emem s1) (emem s2) wptrs aligns vargs vargs' i.
Proof.
  move=> hvs.
  rewrite /alloc_call_arg_aux.
  t_xrbindP=> x /get_PvarP ->.
  case: x => x [] //= _.
  case: opi => [pi|]; last first.
  + case hlx: get_local => //.
    move=> _ _ _ hnreg _ _.
    by rewrite /wf_arg hnreg.
  case hlx: get_local => [pk|//].
  case: pk hlx => // p hlx.
  t_xrbindP=> -[sr ?] /get_sub_region_statusP [hsr ->] /=.
  have /wfr_wf hwf := hsr.
  t_xrbindP=> _ /(check_alignP hwf) halign {}rmap2 hclear _ <- hget /=.
  have /wfr_ptr := hsr.
  have [addr ok_addr] := wf_sub_region_sub_region_addr hwf.
  rewrite hlx => -[_ [[<-] /=]] hgetp.
  rewrite get_gvar_nglob // /get_var /= (hgetp _ ok_addr) /= orbT /=.
  have hget' : get_gvar true gd (evm s1) {| gv := x; gs := Slocal |} = ok (nth (Vbool true) vargs i).
  + have /is_sarrP [len hty] := wfr_type (wf_pmap0.(wf_locals) hlx).
    move: hget; rewrite /get_gvar /= => /get_varP [].
    by rewrite /get_var hty => <- ? /compat_valEl [a] ->.
  (* We have [size_val v1 <= size_slot x] by [have /= hle := size_of_le (type_of_get_gvar_sub hget')].
     The inequality is sufficient for most of the proof.
     But we even have the equality, so let's use it.
  *)
  have hgvalid := check_gvalid_lvar hsr.
  have /(wfr_val hgvalid) [_ /= hty] := hget'.
  move=> [/esym haddr] hwptr hal hdisj.
  rewrite /wf_arg hwptr haddr.
  eexists; split; first by reflexivity.
  split.
  + rewrite hal.
    by apply (halign _ ok_addr).
  + have /= := no_overflow_sub_region_addr hwf ok_addr.
    by rewrite hty.
  + move=> w hb.
    apply (vs_slot_valid hwf.(wfr_slot)).
    apply (zbetween_trans (zbetween_sub_region_addr hwf ok_addr)).
    by rewrite -hty.
  + move=> w hvalid.
    apply: disjoint_zrange_incl_l (vs_disjoint hwf.(wfr_slot) hvalid).
    rewrite hty.
    by apply (zbetween_sub_region_addr hwf ok_addr).
  + move=> hw hgsize.
    move: hclear; rewrite hw => /set_clearP [hwritable _].
    apply: disjoint_zrange_incl_r (writable_not_glob hwf.(wfr_slot) _ hgsize);
      last by rewrite hwf.(wfr_writable).
    rewrite hty.
    by apply (zbetween_sub_region_addr hwf ok_addr).
  by move=> *; (eapply hdisj; first by congruence); try eassumption; reflexivity.
Qed.

Lemma alloc_call_args_aux_wf table rmap vme m0 s1 s2 sao_params args rmap2 l wdb vargs1 vargs2 :
  valid_state table rmap vme m0 s1 s2 ->
  alloc_call_args_aux pmap rmap sao_params args = ok (rmap2, l) ->
  sem_pexprs wdb gd s1 args = ok vargs1 ->
  sem_pexprs wdb [::] s2 (map snd l) = ok vargs2 ->
  (forall i, nth None (map (omap pp_writable) sao_params) i = Some true ->
    forall j vai vaj (pi pj : word Uptr),
    i <> j ->
    isSome (nth None (map (omap pp_writable) sao_params) j) ->
    nth (Vbool true) vargs1 i = vai ->
    nth (Vbool true) vargs1 j = vaj ->
    nth (Vbool true) vargs2 i = Vword pi ->
    nth (Vbool true) vargs2 j = Vword pj ->
    disjoint_zrange pi (size_val vai) pj (size_val vaj)) ->
  wf_args (emem s1) (emem s2)
    (map (omap pp_writable) sao_params)
    (map (oapp pp_align U8) sao_params) vargs1 vargs2.
Proof.
  move=> hvs hallocs ok_vargs1 ok_vargs2 hdisj.
  move=> i.
  (* It is enough to show wf_arg for interesting i *)
  suff: forall writable,
    nth None [seq omap pp_writable i | i <- sao_params] i = Some writable ->
    wf_arg (emem s1) (emem s2)
      [seq omap pp_writable i | i <- sao_params]
      [seq oapp pp_align U8 i | i <- sao_params] vargs1 vargs2 i.
  + rewrite /wf_arg.
    case: nth => [writable|//].
    by apply; reflexivity.
  move=> writable hwritable.
  have := nth_not_default hwritable ltac:(discriminate); rewrite size_map => hi.
  have [hsize1 hsize2] := size_fmapM2 hallocs.
  have [rmap1 [rmap1' [_ [halloc _]]]] :=
    fmapM2_nth None (Pconst 0) (None, Pconst 0) hallocs hi.
  apply (alloc_call_arg_aux_wf (wdb:=wdb) hvs halloc).
  + apply (mapM_nth (Pconst 0) (Vbool true) ok_vargs1).
    by rewrite -hsize1.
  + rewrite -(nth_map _ (Pconst 0)); last by rewrite -hsize2.
    apply (mapM_nth (Pconst 0) (Vbool true) ok_vargs2).
    by rewrite size_map -hsize2.
  + by rewrite (nth_map None).
  + by rewrite (nth_map None).
  exact: hdisj.
Qed.

Lemma alloc_call_arg_aux_sub_region table rmap0 rmap vme m0 s1 s2 opi e1 rmap2 bsr e2 wdb v1 v2 :
  valid_state table rmap0 vme m0 s1 s2 ->
  alloc_call_arg_aux pmap rmap0 rmap opi e1 = ok (rmap2, (bsr, e2)) ->
  sem_pexpr wdb gd s1 e1 = ok v1 ->
  sem_pexpr wdb [::] s2 e2 = ok v2 -> [/\
    forall b sr, bsr = Some (b, sr) ->
      wf_sub_region vme sr (type_of_val v1)
      /\ (forall addr, sub_region_addr vme sr = ok addr -> v2 = Vword addr) &
    forall sr, bsr = Some (true, sr) ->
      incl rmap2 (set_clear_pure rmap sr)].
Proof.
  move=> hvs.
  rewrite /alloc_call_arg_aux.
  t_xrbindP=> x /get_PvarP ->.
  case: x => x [] //= _.
  case: opi => [pi|]; last first.
  + case hlx: get_local => //.
    t_xrbindP=> /check_diffP hnnew _ <- _ _ _.
    by split.
  case hlx: get_local => [pk|//].
  case: pk hlx => // p hlx.
  t_xrbindP=> -[sr _] /get_sub_region_statusP [hsr ->] /=.
  have /wfr_wf hwf := hsr.
  t_xrbindP=> _ _ {}rmap2 hclear <- <- <- hget /=.
  have /wfr_ptr := hsr.
  have [addr ok_addr] := wf_sub_region_sub_region_addr hwf.
  rewrite /get_var_kind /= hlx => -[_ [[<-] /=]] hgetp.
  rewrite get_gvar_nglob // /get_var /= (hgetp _ ok_addr) /= orbT /= => -[<-].
  have hget' : get_gvar true gd (evm s1) {| gv := x; gs := Slocal |} = ok v1.
  + have /is_sarrP [len hty] := wfr_type (wf_pmap0.(wf_locals) hlx).
    move: hget; rewrite /get_gvar /= => /get_varP [].
    by rewrite /get_var hty => <- ? /compat_valEl [a] ->.
  (* We have [size_val v1 <= size_slot x] by [have /= hle := size_of_le (type_of_get_gvar_sub hget')].
     The inequality is sufficient for most of the proof.
     But we even have the equality, so let's use it.
  *)
  have hgvalid := check_gvalid_lvar hsr.
  have /(wfr_val hgvalid) [_ /= hty] := hget'.
  split.
  + move=> _ _ [_ <-].
    split.
    + by rewrite hty.
    rewrite ok_addr.
    move=> _ [<-].
    by reflexivity.
  move=> _ [hw <-].
  move: hclear; rewrite hw => /set_clearP [_ ->].
  by apply incl_refl.
Qed.

(* This predicates states that sub-region [sr] is cleared in [rmap]. It is a bit
   ankward, since we want it to work both for normal sub-regions in [var_region]
   and stkptr sub-regions not in [var_region]. *)
Definition sub_region_cleared (rmap:region_map) vme sr :=
  forall x off,
    valid_offset vme (get_var_status rmap sr.(sr_region) x) off ->
    exists srx, Mvar.get rmap.(var_region) x = Some srx /\
      forall cs csx,
        sem_zone vme sr.(sr_zone) = ok cs ->
        sem_zone vme srx.(sr_zone) = ok csx ->
        0 <= off < csx.(cs_len) ->
        ~ offset_in_concrete_slice cs (csx.(cs_ofs) + off).

Lemma set_clear_pure_sub_region_cleared rmap vme sr ty :
  wfr_WF rmap vme ->
  wfr_STATUS rmap vme ->
  wf_sub_region vme sr ty ->
  sub_region_cleared (set_clear_pure rmap sr) vme sr.
Proof.
  move=> hwfsr hwfst hwf x off.
  rewrite /= get_var_status_set_clear_status eqxx /=.
  case hsrx: (Mvar.get rmap.(var_region) x) => [srx|]; last first.
  + by rewrite /clear_status_map_aux hsrx.
  move=> off_valid.
  exists srx; split=> // cs csx ok_cs ok_csx hoff.
  have hwfs := hwfst sr.(sr_region) x.
  have:= hwf.(wfsr_zone); rewrite /wf_zone ok_cs => -[_ [<-] wf_cs].
  by have [_ +] :=
    valid_offset_clear_status_map_aux hwfs hsrx ok_csx ok_cs hoff off_valid.
Qed.

(* inclusion of var_region in opposite direction to region_var *)
Lemma incl_sub_region_cleared rmap1 rmap2 vme sr :
  Mvar.incl (fun _ => eq_op) rmap2.(var_region) rmap1.(var_region) ->
  Mr.incl (fun _ => incl_status_map) rmap1.(region_var) rmap2.(region_var) ->
  wfr_STATUS rmap1 vme ->
  sub_region_cleared rmap2 vme sr ->
  sub_region_cleared rmap1 vme sr.
Proof.
  move=> hinclr hincls hwfst1 hcleared2 x off off_valid1.
  have hwfs := hwfst1 sr.(sr_region) x.
  have {}hincls:
    incl_status
      (get_var_status rmap1 sr.(sr_region) x)
      (get_var_status rmap2 sr.(sr_region) x).
  + have /Mr.inclP /(_ sr.(sr_region)) := hincls.
    rewrite /get_var_status /get_status_map /get_status.
    case: Mr.get => [sm1|//].
    case: Mr.get => [sm2|//].
    move=> /Mvar.inclP /(_ x).
    case: Mvar.get => [status1|//].
    by case: Mvar.get => [status2|//].
  have /(incl_statusP hincls hwfs) off_valid2 := off_valid1.
  have [srx2 [hsrx2 {}hcleared2]] := hcleared2 x off off_valid2.
  have /Mvar.inclP /(_ x) := hinclr.
  rewrite hsrx2.
  case hsrx1: Mvar.get => [srx1|//] /eqP ?; subst srx1.
  by exists srx2.
Qed.

Lemma alloc_call_args_aux_sub_region table rmap vme m0 s1 s2 sao_params args rmap2 l wdb vargs1 vargs2 :
  valid_state table rmap vme m0 s1 s2 ->
  alloc_call_args_aux pmap rmap sao_params args = ok (rmap2, l) ->
  sem_pexprs wdb gd s1 args = ok vargs1 ->
  sem_pexprs wdb [::] s2 (map snd l) = ok vargs2 -> [/\
    Forall3 (fun bsr varg1 varg2 => forall (b:bool) (sr:sub_region), bsr = Some (b, sr) ->
      wf_sub_region vme sr (type_of_val varg1)
      /\ (forall addr, sub_region_addr vme sr = ok addr -> varg2 = Vword addr)) (map fst l) vargs1 vargs2 &
    List.Forall2 (fun bsr varg1 => forall sr, bsr = Some (true, sr) ->
      sub_region_cleared rmap2 vme sr) (map fst l) vargs1].
Proof.
  move=> hvs.
  have: wfr_STATUS rmap vme by apply wfr_status.
  have: wfr_WF rmap vme by apply wfr_wf.
  have: forall r, Mr.get rmap r <> None -> Mr.get rmap r <> None by done.
  rewrite /alloc_call_args_aux.
  elim: sao_params args {-1 5}rmap rmap2 l vargs1 vargs2.
  + move=> [|//] /= rmap0 _ _ _ _ _ _ _ [<- <-] [<-] [<-].
    by split; constructor.
  move=> opi sao_params ih [//|arg args] rmap0 /=.
  t_xrbindP=> _ _ _ + hnnone hwfsr0 hwfst0 [rmap1 [bsr e]] halloc [rmap2 l] /=
    hallocs <- <- varg1 hvarg1 vargs1 hvargs1 <- /=.
  t_xrbindP=> _ varg2 hvarg2 vargs2 hvargs2 <-.
  have [haddr hclear] := alloc_call_arg_aux_sub_region hvs halloc hvarg1 hvarg2.
  have [hincl hinclr hnnone2] := alloc_call_arg_aux_incl hnnone halloc.
  have hwfsr := [elaborate wfr_wf].
  have [hwfsr1 hwfst1] :=
    alloc_call_arg_aux_wfr_STATUS hwfsr hwfsr0 hwfst0 halloc.
  have [haddrs hclears] :=
    ih _ _ _ _ _ _ hnnone2 hwfsr1 hwfst1 hallocs hvargs1 hvargs2.
  split; constructor=> //.
  have [hincl2 hinclr2] := alloc_call_args_aux_incl_aux hnnone2 hallocs.
  move=> sr /[dup] /haddr [hwf _] /hclear hincl_clear.
  apply (incl_sub_region_cleared (rmap2 := set_clear_pure rmap0 sr)).
  + apply /Mvar.inclP => x /=.
    case hsrx: Mvar.get => [srx|//].
    by move: hsrx => /hinclr /hinclr2 ->.
  + by have /andP [_ +] := incl_trans hincl2 hincl_clear.
  + by apply (alloc_call_args_aux_wfr_STATUS_aux hwfsr hwfsr1 hwfst1 hallocs).
  by apply: (set_clear_pure_sub_region_cleared hwfsr0 hwfst0 hwf).
Qed.

Lemma disj_sub_regions_sym sr1 sr2 : disj_sub_regions sr1 sr2 = disj_sub_regions sr2 sr1.
Proof. by rewrite /disj_sub_regions /region_same eq_sym disjoint_zones_sym. Qed.

(* we could benefit from [seq.allrel] but it exists only in recent versions *)
Lemma check_all_disjP notwritables writables srs :
  check_all_disj notwritables writables srs -> [/\
  forall b1 sr1 sr2, Some (b1, sr1) \in (map fst srs) -> sr2 \in writables -> disj_sub_regions sr1 sr2,
  forall sr1 sr2, Some (true, sr1) \in (map fst srs) -> sr2 \in notwritables -> disj_sub_regions sr1 sr2 &
  forall i1 sr1 i2 b2 sr2, nth None (map fst srs) i1 = Some (true, sr1) -> nth None (map fst srs) i2 = Some (b2, sr2) ->
    i1 <> i2 -> disj_sub_regions sr1 sr2].
Proof.
  elim: srs notwritables writables.
  + move=> notwritables writables _.
    split=> // i1 b1 sr1 i2 b2 sr2.
    by rewrite nth_nil.
  move=> [bsr e] srs ih notwritables writables /=.
  case: bsr => [[b sr]|]; last first.
  + move=> /ih [ih1 ih2 ih3].
    split.
    + move=> b1 sr1 sr2.
      rewrite in_cons /=.
      by apply ih1.
    + move=> sr1 sr2.
      rewrite in_cons /=.
      by apply ih2.
    move=> [//|i1] sr1 [//|i2] b2 sr2 /= hnth1 hnth2 hneq.
    by apply: ih3 hnth1 hnth2 ltac:(congruence).
  case: allP => // hdisj.
  case: b; last first.
  + move=> /ih [ih1 ih2 ih3].
    split.
    + move=> b1 sr1 sr2.
      rewrite in_cons => /orP [/eqP [_ ->]|hin1] hin2.
      + by apply hdisj.
      by apply: ih1 hin1 hin2.
    + move=> sr1 sr2.
      rewrite in_cons /= => hin1 hin2.
      apply ih2 => //.
      rewrite in_cons.
      by apply /orP; right.
    move=> [//|i1] sr1 [|i2] b2 sr2 /=.
    + move=> hnth1 [_ <-] _.
      apply ih2; last by apply mem_head.
      rewrite -hnth1.
      apply mem_nth.
      by apply (nth_not_default hnth1 ltac:(discriminate)).
    move=> hnth1 hnth2 hneq.
    by apply: ih3 hnth1 hnth2 ltac:(congruence).
  case: allP => // hdisj2.
  move=> /ih [ih1 ih2 ih3].
  split.
  + move=> b1 sr1 sr2.
    rewrite in_cons => /orP [/eqP [_ ->]|hin1] hin2.
    + by apply hdisj.
    apply (ih1 _ _ _ hin1).
    rewrite in_cons.
    by apply /orP; right.
  + move=> sr1 sr2.
    rewrite in_cons => /orP [/eqP [->]|hin1] hin2.
    + by apply hdisj2.
    by apply ih2.
  move=> i1 sr1 i2 b2 sr2.
  case: i1 => [|i1].
  + case: i2 => [//|i2].
    move=> /= [<-] hnth2 _.
    rewrite disj_sub_regions_sym.
    apply (ih1 b2); last by apply mem_head.
    rewrite -hnth2.
    apply mem_nth.
    by apply (nth_not_default hnth2 ltac:(discriminate)).
  move=> /= hnth1.
  case: i2 => [|i2].
  + move=> [_ <-] _.
    apply (ih1 true); last by apply mem_head.
    rewrite -hnth1.
    apply mem_nth.
    by apply (nth_not_default hnth1 ltac:(discriminate)).
  move=> /= hnth2 hneq.
  apply: ih3 hnth1 hnth2 ltac:(congruence).
Qed.

(* TODO: remove disjoint_symbolic_zone and express everything in terms of
   concrete_slice? *)
Lemma disjoint_zonesP vme z1 z2 :
  disjoint_zones z1 z2 ->
  disjoint_symbolic_zone vme z1 z2.
Proof.
  elim: z1 z2 => [|s1 z1 ih1] [|s2 z2] //=.
  case: eqP => [<-|_].
  + move=> hdisj.
    have z1_nnil: z1 <> [::].
    + by case: (z1) hdisj.
    have z2_nnil: z2 <> [::].
    + by case: (z1) (z2) hdisj => [|??] [|??] /=.
    by apply (disjoint_symbolic_zone_cons z1_nnil z2_nnil (ih1 _ hdisj)).
  case hle1: (odflt _ _).
  + move=> _.
    apply disjoint_symbolic_slice_zone.
    by apply symbolic_slice_ble_disjoint.
  case hle2: (odflt _ _) => // _.
  apply disjoint_symbolic_slice_zone.
  apply disjoint_symbolic_slice_sym.
  by apply symbolic_slice_ble_disjoint.
Qed.

Lemma disjoint_symbolic_zone_disjoint_zrange vme sr1 ty1 sr2 ty2 addr1 addr2 :
  wf_sub_region vme sr1 ty1 ->
  sub_region_addr vme sr1 = ok addr1 ->
  wf_sub_region vme sr2 ty2 ->
  sub_region_addr vme sr2 = ok addr2 ->
  sr1.(sr_region) = sr2.(sr_region) ->
  disjoint_symbolic_zone vme sr1.(sr_zone) sr2.(sr_zone) ->
  disjoint_zrange addr1 (size_of ty1) addr2 (size_of ty2).
Proof.
  move=> hwf1 ok_addr1 hwf2 ok_addr2 heq hdisj.
  have [cs1 ok_cs1 wf_cs1] := hwf1.(wfsr_zone).
  have := wunsigned_sub_region_addr hwf1 ok_cs1.
  rewrite ok_addr1 => -[_ [<-] haddr1].
  have [cs2 ok_cs2 wf_cs2] := hwf2.(wfsr_zone).
  have := wunsigned_sub_region_addr hwf2 ok_cs2.
  rewrite ok_addr2 => -[_ [<-] haddr2].
  have := addr_no_overflow (wfr_slot hwf1).
  have := addr_no_overflow (wfr_slot hwf2).
  have := hdisj _ _ ok_cs1 ok_cs2.
  rewrite /disjoint_concrete_slice /disjoint_zrange /no_overflow !zify /=.
  rewrite haddr1 haddr2.
  have := wf_cs1.(wfcs_len).
  have := wf_cs2.(wfcs_len).
  have := wf_cs1.(wfcs_ofs).
  have := wf_cs2.(wfcs_ofs).
  rewrite heq.
  by split; rewrite ?zify; lia.
Qed.

Lemma disj_sub_regions_disjoint_zrange vme sr1 sr2 ty1 ty2 addr1 addr2 :
  wf_sub_region vme sr1 ty1 ->
  sub_region_addr vme sr1 = ok addr1 ->
  wf_sub_region vme sr2 ty2 ->
  sub_region_addr vme sr2 = ok addr2 ->
  disj_sub_regions sr1 sr2 ->
  sr1.(sr_region).(r_writable) ->
  disjoint_zrange addr1 (size_of ty1) addr2 (size_of ty2).
Proof.
  move=> hwf1 haddr1 hwf2 haddr2 hdisj hw.
  move: hdisj; rewrite /disj_sub_regions /region_same.
  case: eqP => heqr /=.
  + move=> /(disjoint_zonesP (vme:=vme)) hdisj.
    apply: (disjoint_symbolic_zone_disjoint_zrange hwf1 haddr1 hwf2 haddr2 _ hdisj).
    by apply (wf_region_slot_inj hwf1 hwf2).
  move=> _.
  by apply (distinct_regions_disjoint_zrange hwf1 haddr1 hwf2 haddr2 ltac:(congruence) hw).
Qed.

Lemma disj_sub_regions_disjoint_values vme (srs:seq (option (bool * sub_region))) sao_params vargs1 vargs2 :
  (forall i1 sr1 i2 b2 sr2, nth None srs i1 = Some (true, sr1) -> nth None srs i2 = Some (b2, sr2) ->
    i1 <> i2 -> disj_sub_regions sr1 sr2) ->
  List.Forall2 (fun opi bsr => forall pi, opi = Some pi -> exists sr, bsr = Some (pi.(pp_writable), sr)) sao_params srs ->
  List.Forall (fun bsr => forall sr, bsr = Some (true, sr) -> sr.(sr_region).(r_writable)) srs ->
  Forall3 (fun bsr varg1 varg2 => forall (b:bool) (sr:sub_region), bsr = Some (b, sr) ->
    wf_sub_region vme sr (type_of_val varg1)
    /\ (forall addr, sub_region_addr vme sr = ok addr -> varg2 = Vword addr)) srs vargs1 vargs2 ->
  forall i, nth None (map (omap pp_writable) sao_params) i = Some true ->
    forall j vai vaj (pi pj : word Uptr),
    i <> j ->
    isSome (nth None (map (omap pp_writable) sao_params) j) ->
    nth (Vbool true) vargs1 i = vai ->
    nth (Vbool true) vargs1 j = vaj ->
    nth (Vbool true) vargs2 i = Vword pi ->
    nth (Vbool true) vargs2 j = Vword pj ->
    disjoint_zrange pi (size_val vai) pj (size_val vaj).
Proof.
  move=> hdisj hnnone hwritable haddr.
  move=> i hwi j vai vaj pi pj neq_ij /isSomeP [wj hwj] hvai hvaj hpi hpj.
  have := nth_not_default hwi ltac:(discriminate); rewrite size_map => hi.
  have := nth_not_default hwj ltac:(discriminate); rewrite size_map => hj.
  move: hwi; rewrite (nth_map None) // => /oseq.obindI [pii [hpii [hwi]]].
  move: hwj; rewrite (nth_map None) // => /oseq.obindI [pij [hpij _]].
  have := Forall2_nth hnnone None None.
  move=> /[dup].
  move=> /(_ _ hi _ hpii); rewrite hwi => -[sri hsri].
  move=> /(_ _ hj _ hpij) [srj hsrj].
  have /InP hini := mem_nth None (nth_not_default hsri ltac:(discriminate)).
  have /List.Forall_forall -/(_ _ hini _ hsri) hwi' := hwritable.
  have := Forall3_nth haddr None (Vbool true) (Vbool true).
  move=> /[dup].
  move=> /(_ _ (nth_not_default hsri ltac:(discriminate)) _ _ hsri).
  rewrite hpi hvai => -[] hwfi.
  have [addri ok_addri] := wf_sub_region_sub_region_addr hwfi.
  move=> /(_ _ ok_addri) [?]; subst pi.
  move=> /(_ _ (nth_not_default hsrj ltac:(discriminate)) _ _ hsrj).
  rewrite hpj hvaj => -[] hwfj.
  have [addrj ok_addrj] := wf_sub_region_sub_region_addr hwfj.
  move=> /(_ _ ok_addrj) [?]; subst pj.
  apply (disj_sub_regions_disjoint_zrange hwfi ok_addri hwfj ok_addrj) => //.
  by apply: hdisj hsri hsrj neq_ij.
Qed.

Lemma alloc_call_argsE rmap sao_params args rmap2 l :
  alloc_call_args pmap rmap sao_params args = ok (rmap2, l) ->
  alloc_call_args_aux pmap rmap sao_params args = ok (rmap2, l) /\
  check_all_disj [::] [::] l.
Proof.
  rewrite /alloc_call_args.
  by t_xrbindP=> -[{}rmap2 {}l] halloc hdisj [<- <-].
Qed.

(* Full spec *)
Lemma alloc_call_argsP table rmap vme m0 s1 s2 sao_params args rmap2 l wdb vargs1 :
  valid_state table rmap vme m0 s1 s2 ->
  alloc_call_args pmap rmap sao_params args = ok (rmap2, l) ->
  sem_pexprs wdb gd s1 args = ok vargs1 ->
  exists vargs2, [/\
    sem_pexprs wdb [::] s2 (map snd l) = ok vargs2,
    wf_args (emem s1) (emem s2)
      (map (omap pp_writable) sao_params)
      (map (oapp pp_align U8) sao_params) vargs1 vargs2,
    Forall3 (value_eq_or_in_mem (emem s2)) sao_params vargs1 vargs2,
    Forall3 (fun bsr varg1 varg2 => forall (b:bool) (sr:sub_region), bsr = Some (b, sr) ->
      wf_sub_region vme sr (type_of_val varg1) /\
      forall addr, sub_region_addr vme sr = ok addr -> varg2 = Vword addr) (map fst l) vargs1 vargs2,
    List.Forall (fun bsr => forall b sr, bsr = Some (b, sr) -> wf_vars_zone table.(vars) sr.(sr_zone)) (map fst l) &
    List.Forall2 (fun bsr varg1 => forall sr, bsr = Some (true, sr) ->
      sub_region_cleared rmap2 vme sr) (map fst l) vargs1].
Proof.
  move=> hvs /alloc_call_argsE [halloc hdisj] hvargs1.
  have [vargs2 [hvargs2 heqinmems]] := alloc_call_args_aux_uincl hvs halloc hvargs1.
  have [haddr hclear] := alloc_call_args_aux_sub_region hvs halloc hvargs1 hvargs2.
  have hvarsz := alloc_call_args_aux_wfr_VARS_ZONE_sub_region halloc hvs.(vs_wf_region).(wfr_vars_zone).
  have [_ _ {}hdisj] := check_all_disjP hdisj.
  have {}hdisj :=
    disj_sub_regions_disjoint_values hdisj
      (alloc_call_args_aux_not_None halloc)
      (alloc_call_args_aux_writable halloc) haddr.
  have hwf := alloc_call_args_aux_wf hvs halloc hvargs1 hvargs2 hdisj.
  by exists vargs2; split.
Qed.

Lemma mem_unchanged_holed_rmap vme m0 s1 s2 mem1 mem2 l :
  valid_incl m0 (emem s2) ->
  validw (emem s1) =3 validw mem1 ->
  List.Forall (fun '(sr, ty) => wf_sub_region vme sr ty /\ sr.(sr_region).(r_writable)) l ->
  (forall p,
    validw (emem s2) Aligned p U8 -> ~ validw (emem s1) Aligned p U8 ->
    List.Forall (fun '(sr, ty) =>
      forall addr, sub_region_addr vme sr = ok addr ->
      disjoint_zrange addr (size_of ty) p (wsize_size U8)) l ->
    read mem2 Aligned p U8 = read (emem s2) Aligned p U8) ->
  mem_unchanged (emem s1) m0 (emem s2) ->
  mem_unchanged mem1 m0 mem2.
Proof.
  move=> hincl hvalideq1 hlwf hlunch hunch p hvalid1 hvalid2 hdisj.
  rewrite -hvalideq1 in hvalid2.
  rewrite (hunch _ hvalid1 hvalid2 hdisj).
  symmetry; apply hlunch => //.
  + by apply hincl.
  apply List.Forall_forall => -[sr ty] hin.
  have /List.Forall_forall -/(_ _ hin) [hwf hw] := hlwf.
  have [addr ok_addr] := wf_sub_region_sub_region_addr hwf.
  rewrite ok_addr => _ [<-].
  apply (disjoint_zrange_incl_l (zbetween_sub_region_addr hwf ok_addr)).
  apply (hdisj _ hwf.(wfr_slot)).
  by rewrite hwf.(wfr_writable).
Qed.

(* "holed" because [rmap.(region_var)] does not contain any information about the sub-regions in [l]. *)
Lemma eq_read_holed_rmap table rmap vme m0 s1 s2 mem2 l sr ty addr off :
  valid_state table rmap vme m0 s1 s2 ->
  List.Forall (fun '(sr, ty) => wf_sub_region vme sr ty /\ sr.(sr_region).(r_writable)) l ->
  (forall p,
    validw (emem s2) Aligned p U8 -> ~ validw (emem s1) Aligned p U8 ->
    List.Forall (fun '(sr, ty) =>
      forall addr, sub_region_addr vme sr = ok addr ->
      disjoint_zrange addr (size_of ty) p (wsize_size U8)) l ->
    read mem2 Aligned p U8 = read (emem s2) Aligned p U8) ->
  List.Forall (fun '(sr, ty) => sub_region_cleared rmap vme sr) l ->
  wf_sub_region vme sr ty ->
  sub_region_addr vme sr = ok addr ->
  0 <= off /\ off < size_of ty ->
  (sr.(sr_region).(r_writable) ->
    exists2 x,
      Mvar.get rmap.(var_region) x = None \/ Mvar.get rmap.(var_region) x = Some sr &
      valid_offset vme (get_var_status rmap sr.(sr_region) x) off) ->
  read mem2 Aligned (addr + wrepr _ off)%R U8 = read (emem s2) Aligned (addr + wrepr _ off)%R U8.
Proof.
  move=> hvs hlwf hlunch hldisj hwf haddr hoff off_valid.
  case:(hvs) => hscs hvalid hdisj hincl hincl2 hunch hrip hrsp heqvm hwfr hwft heqmem hglobv htop.
  apply hlunch.
  + apply (hvalid _ _ hwf.(wfr_slot)).
    apply: between_byte hoff.
    + by apply (no_overflow_sub_region_addr hwf haddr).
    by apply (zbetween_sub_region_addr hwf haddr).
  + move=> hvalid'.
    have := hdisj _ _ hwf.(wfr_slot) hvalid'.
    apply zbetween_not_disjoint_zrange => //.
    apply: between_byte hoff.
    + by apply (no_overflow_sub_region_addr hwf haddr).
    by apply (zbetween_sub_region_addr hwf haddr).
  apply List.Forall_forall => -[sr2 ty2] hin2 addr2 haddr2.
  have /List.Forall_forall -/(_ _ hin2) hdisj2 := hldisj.
  have /List.Forall_forall -/(_ _ hin2) [hwf2 hw2] := hlwf.

  have ok_off: sem_sexpr vme (Sconst off) >>= to_int = ok off.
  + by [].
  have hoff': 0 <= off ∧ off + size_of sword8 <= size_of ty.
  + by rewrite /= wsize8; lia.
  have hwf' := sub_region_at_ofs_wf hwf ok_off hoff'.
  have haddr' := sub_region_addr_offset hwf ok_off hoff' haddr.
  change (wsize_size U8) with (size_of sword8).

  case: (sr2.(sr_region) =P sr.(sr_region)) => heqr.
  + move: off_valid; rewrite -heqr => /(_ hw2) [x hsr off_valid].
    apply (disjoint_symbolic_zone_disjoint_zrange hwf2 haddr2 hwf' haddr' heqr).
    have [+ []] := hdisj2 x off off_valid.
    case: hsr => -> // _ [<-] {}hdisj2.
    have [cs ok_cs wf_cs] := hwf.(wfsr_zone).
    have [cs2 ok_cs2 wf_cs2] := hwf2.(wfsr_zone).
    have hoff'': 0 <= off < cs.(cs_len).
    + have := wf_cs.(wfcs_len).
      by lia.
    have off_nin := hdisj2 _ _ ok_cs2 ok_cs hoff''.
    have [cs' [ok_cs' _ hsub]] := sub_zone_at_ofsP ok_cs wf_cs ok_off hoff'.
    rewrite /disjoint_symbolic_zone ok_cs' ok_cs2 => _ _ [<-] [<-].
    move: hsub; rewrite /sub_concrete_slice /=; case: ifP => // _ [<-].
    move: off_nin;
      rewrite /offset_in_concrete_slice /disjoint_concrete_slice /= wsize8 !zify.
    by lia.
  by apply (distinct_regions_disjoint_zrange hwf2 haddr2 hwf' haddr' heqr hw2).
Qed.

Lemma wfr_VAL_holed_rmap table rmap vme m0 s1 s2 mem1 mem2 l :
  valid_state table rmap vme m0 s1 s2 ->
  List.Forall (fun '(sr, ty) => wf_sub_region vme sr ty /\ sr.(sr_region).(r_writable)) l ->
  (forall p,
    validw (emem s2) Aligned p U8 -> ~ validw (emem s1) Aligned p U8 ->
    List.Forall (fun '(sr, ty) =>
      forall addr, sub_region_addr vme sr = ok addr ->
      disjoint_zrange addr (size_of ty) p (wsize_size U8)) l ->
    read mem2 Aligned p U8 = read (emem s2) Aligned p U8) ->
  List.Forall (fun '(sr, ty) => sub_region_cleared rmap vme sr) l ->
  wfr_VAL rmap vme (with_mem s1 mem1) (with_mem s2 mem2).
Proof.
  move=> hvs hlwf hlunch hlincl.
  move=> x sr status v /= hgvalid /(wfr_val hgvalid) [hread hty].
  have /(check_gvalid_wf wfr_wf) /= hwf := hgvalid.
  split=> // off addr w ok_addr off_valid /[dup] /get_val_byte_bound; rewrite hty => hoff hget.
  rewrite -(hread _ _ _ ok_addr off_valid hget).
  apply (eq_read_holed_rmap hvs hlwf hlunch hlincl hwf ok_addr hoff).
  move=> hw.
  have hnglob := check_gvalid_writable hgvalid hw.
  rewrite -(mk_lvar_nglob hnglob) in hgvalid.
  have [hsr hstatus] := check_gvalid_lvar_inv hgvalid.
  exists x.(gv).(v_var).
  + by right.
  by rewrite -hstatus.
Qed.

Lemma wfr_PTR_holed_rmap table rmap vme m0 s1 s2 mem2 l :
  valid_state table rmap vme m0 s1 s2 ->
  List.Forall (fun '(sr, ty) => wf_sub_region vme sr ty /\ sr.(sr_region).(r_writable)) l ->
  (forall p,
    validw (emem s2) Aligned p U8 -> ~ validw (emem s1) Aligned p U8 ->
    List.Forall (fun '(sr, ty) =>
      forall addr, sub_region_addr vme sr = ok addr ->
      disjoint_zrange addr (size_of ty) p (wsize_size U8)) l ->
    read mem2 Aligned p U8 = read (emem s2) Aligned p U8) ->
  List.Forall (fun '(sr, ty) => sub_region_cleared rmap vme sr) l ->
  wfr_PTR rmap vme (with_mem s2 mem2).
Proof.
  move=> hvs hlwf hlunch hlincl.
  move=> x sr /wfr_ptr [pk [hlx hpk]].
  exists pk; split=> //.
  case: pk hlx hpk => // s ofs ws cs f hlx /= hpk hcheck paddr addr hpaddr haddr.
  rewrite -(hpk hcheck _ _ hpaddr haddr).
  apply eq_read => al i hi; rewrite addE.
  have /wf_locals /= hlocal := hlx.
  have hwfs := sub_region_stkptr_wf vme hlocal.
  rewrite !(read8_alignment Aligned).
  apply (eq_read_holed_rmap hvs hlwf hlunch hlincl hwfs hpaddr hi).
  case heq: (Mvar.get rmap.(var_region) f) => [srf|].
  + by case (var_region_not_new wfr_ptr heq (wfs_new hlocal)).
  move=> _; exists f.
  + by left.
  move: hcheck; rewrite /check_stack_ptr.
  by move=> /is_validP ->.
Qed.

Lemma valid_state_holed_rmap table rmap vme m0 s1 s2 mem1 mem2 l :
  valid_state table rmap vme m0 s1 s2 ->
  validw (emem s1) =3 validw mem1 ->
  stack_stable (emem s2) mem2 ->
  validw (emem s2) =3 validw mem2 ->
  eq_mem_source mem1 mem2 ->
  List.Forall (fun '(sr, ty) => wf_sub_region vme sr ty /\ sr.(sr_region).(r_writable)) l ->
  (forall p,
    validw (emem s2) Aligned p U8 -> ~ validw (emem s1) Aligned p U8 ->
    List.Forall (fun '(sr, ty) =>
      forall addr, sub_region_addr vme sr = ok addr ->
      disjoint_zrange addr (size_of ty) p (wsize_size U8)) l ->
    read mem2 Aligned p U8 = read (emem s2) Aligned p U8) ->
  List.Forall (fun '(sr, ty) => sub_region_cleared rmap vme sr) l ->
  valid_state table rmap vme m0 (with_mem s1 mem1) (with_mem s2 mem2).
Proof.
  move=> hvs hvalideq1 hss2 hvalideq2 heqmem_ hlwf hlunch hlincl.
  case:(hvs) => hscs hvalid hdisj hincl hincl2 hunch hrip hrsp heqvm hwft hwfr heqmem hglobv htop.
  constructor=> //=.
  + by move=> ??; rewrite -hvalideq2; apply hvalid.
  + by move=> ??; rewrite -hvalideq1; apply hdisj.
  + by move=> ?; rewrite -hvalideq1 -hvalideq2; apply hincl.
  + by move=> ?; rewrite -hvalideq2; apply hincl2.
  + by apply (mem_unchanged_holed_rmap hincl2 hvalideq1 hlwf hlunch hunch).
  + case: (hwfr) => hwfsr hwfst hvarsz hvarss hval hptr; split=> //.
    + by apply (wfr_VAL_holed_rmap hvs hlwf hlunch hlincl).
    by apply (wfr_PTR_holed_rmap hvs hlwf hlunch hlincl).
  by rewrite -(ss_top_stack hss2).
Qed.

Lemma check_lval_reg_callP r tt :
  check_lval_reg_call pmap r = ok tt ->
    (exists ii ty, r = Lnone ii ty) \/
    exists x,
      [/\ r = Lvar x, Mvar.get pmap.(locals) x = None & ~ Sv.In x pmap.(vnew)].
Proof.
  rewrite /check_lval_reg_call.
  case: r => //.
  + move=> ii ty _.
    by left; exists ii, ty.
  move=> x.
  case heq: get_local => [//|].
  t_xrbindP=> /check_diffP ? _.
  by right; exists x.
Qed.

Lemma wfr_VARS_ZONE_alloc_lval_call srs rmap r oi rmap2 r2 vars :
  alloc_lval_call pmap srs rmap r oi = ok (rmap2, r2) ->
  List.Forall (fun bsr =>
    forall b sr, bsr = Some (b, sr) -> wf_vars_zone vars sr.(sr_zone)) (map fst srs) ->
  wfr_VARS_ZONE vars rmap ->
  wfr_VARS_ZONE vars rmap2.
Proof.
  rewrite /alloc_lval_call.
  case: oi => [i|]; last first.
  + by t_xrbindP=> _ <- _.
  case hnth: nth => [[[b sr]|//] ?].
  have {}hnth: nth None (map fst srs) i = Some (b, sr).
  + rewrite (nth_map (None, Pconst 0)) ?hnth //.
    by apply (nth_not_default hnth ltac:(discriminate)).
  case: r => //.
  + by move=> _ _ [<- _].
  t_xrbindP=> x _ _ <- _.
  move=> hforall hvarz.
  apply wfr_VARS_ZONE_set_move => //.
  by apply (Forall_nth hforall None (nth_not_default hnth ltac:(discriminate)) _ _ hnth).
Qed.

Lemma wfr_VARS_STATUS_alloc_lval_call srs rmap r oi rmap2 r2 vars :
  alloc_lval_call pmap srs rmap r oi = ok (rmap2, r2) ->
  wfr_VARS_STATUS vars rmap ->
  wfr_VARS_STATUS vars rmap2.
Proof.
  rewrite /alloc_lval_call.
  case: oi => [i|]; last first.
  + by t_xrbindP=> _ <- _.
  case hnth: nth => [[[b sr]|//] ?].
  case: r => //.
  + by move=> _ _ [<- _].
  t_xrbindP=> x _ _ <- _.
  move=> hvarz.
  by apply wfr_VARS_STATUS_set_move_status.
Qed.

Lemma alloc_lval_callP table rmap vme m0 s1 s2 srs r oi rmap2 r2 vargs1 vargs2 vres1 vres2 wdb s1' :
  valid_state table rmap vme m0 s1 s2 ->
  alloc_lval_call pmap srs rmap r oi = ok (rmap2, r2) ->
  Forall3 (fun bsr varg1 varg2 => forall (b:bool) (sr:sub_region), bsr = Some (b, sr) ->
    wf_sub_region vme sr (type_of_val varg1) /\
    forall addr, sub_region_addr vme sr = ok addr -> varg2 = Vword addr) (map fst srs) vargs1 vargs2 ->
  List.Forall (fun bsr => forall b sr, bsr = Some (b, sr) -> wf_vars_zone table.(vars) sr.(sr_zone)) (map fst srs) ->
  wf_result vargs1 vargs2 oi vres1 vres2 ->
  value_eq_or_in_mem (emem s2) oi vres1 vres2 ->
  write_lval wdb gd r vres1 s1 = ok s1' ->
  exists s2', [/\
    write_lval wdb [::] r2 vres2 s2 = ok s2' &
    valid_state (remove_binding_lval table r) rmap2 vme m0 s1' s2'].
Proof.
  move=> hvs halloc haddr hvarsz hresult heqinmem hs1'.
  move: halloc; rewrite /alloc_lval_call.
  case: oi hresult heqinmem => [i|]; last first.
  + move=> _ ->.
    t_xrbindP=> /check_lval_reg_callP hcheck <- <-.
    case: hcheck.
    + move=> [ii [ty ?]]; subst r.
      by move /write_noneP : hs1';rewrite /= /write_none => -[-> -> ->]; exists s2.
    move=> [x [? hlx hnnew]]; subst r.
    move /write_varP: hs1' => [-> hdb h] /=.
    rewrite (write_var_truncate hdb h) //.
    by eexists;(split;first by reflexivity) => //; apply valid_state_set_var.
  move=> /= hresp [w [? hread]]; subst vres2.
  case hnth: nth => [[[b sr]|//] ?].
  have {}hnth: nth None (map fst srs) i = Some (b, sr).
  + rewrite (nth_map (None, Pconst 0)) ?hnth //.
    by apply (nth_not_default hnth ltac:(discriminate)).
  case: r hs1' => //.
  + move=> ii ty /= /write_noneP [-> ? hdb][<- <-] /=; rewrite /write_none /=.
    by rewrite cmp_le_refl /= /DB !orbT /=; eexists.
  t_xrbindP=> x hs1' p /get_regptrP hlx <- <-.
  have /wf_locals hlocal := hlx.
  move/write_varP: hs1' => [-> hdb h].
  have /is_sarrP [nx hty] := hlocal.(wfr_type).
  have :=
    Forall3_nth haddr None (Vbool true) (Vbool true) (nth_not_default hnth ltac:(discriminate)) _ _ hnth.
  rewrite -hresp.(wrp_args) => -[] hwf.
  have [addr ok_addr] := wf_sub_region_sub_region_addr hwf.
  move=> /(_ _ ok_addr) [?]; subst w.
  set vp := Vword addr.
  exists (with_vm s2 (evm s2).[p <- vp]).
  have : type_of_val vp = vtype p by rewrite hlocal.(wfr_rtype).
  split; first by apply write_var_eq_type => //; rewrite /DB /= orbT.
  have : type_of_val vres1 = sarr nx.
  + by move/vm_truncate_valEl_wdb: h; rewrite hty /= => -[a ->].
  move=> /type_of_valI -[a' ?]; subst vres1.
  have /vm_truncate_valE_wdb [? heq]:= h.
  apply: (valid_state_set_move_regptr hvs _ ok_addr _ _ _ hlx) => //.
  + apply: wf_sub_region_subtype hwf.
    apply: subtype_trans hresp.(wrp_subtype).
    by rewrite hty.
  + by apply (Forall_nth hvarsz None (nth_not_default hnth ltac:(discriminate)) _ _ hnth).
  rewrite heq; split=> // off addr' w ok_addr' _.
  move: ok_addr'; rewrite ok_addr => -[<-].
  by apply hread.
Qed.

Lemma alloc_lval_call_lv_write_mem srs rmap r oi rmap2 r2 :
  alloc_lval_call pmap srs rmap r oi = ok (rmap2, r2) ->
  ~~ lv_write_mem r2.
Proof.
  rewrite /alloc_lval_call.
  case: oi => [i|].
  + case: nth => [[[b sr]|//] e].
    case: r => //.
    + by move=> ii ty [_ <-].
    by t_xrbindP=> _ p _ _ <-.
  t_xrbindP=> /check_lval_reg_callP hcheck _ <-.
  case: hcheck.
  + by move=> [_ [_ ->]] /=.
  by move=> [x [-> _ _]].
Qed.

Lemma remove_binding_lval_vars table r :
  (remove_binding_lval table r).(vars) = table.(vars).
Proof. by case: r. Qed.

Lemma remove_binding_lvals_vars table rs :
  (remove_binding_lvals table rs).(vars) = table.(vars).
Proof.
  elim: rs table => [//|r rs ih] table /=.
  by rewrite ih remove_binding_lval_vars.
Qed.

Lemma wfr_VARS_ZONE_alloc_call_res rmap srs ret_pos rs rmap2 rs2 vars :
  alloc_call_res pmap rmap srs ret_pos rs = ok (rmap2, rs2) ->
  List.Forall (fun bsr =>
    forall b sr, bsr = Some (b, sr) -> wf_vars_zone vars sr.(sr_zone)) (map fst srs) ->
  wfr_VARS_ZONE vars rmap ->
  wfr_VARS_ZONE vars rmap2.
Proof.
  move=> + hforall.
  elim: rs ret_pos rmap rmap2 rs2 => [|r rs ih] [|oi ret_pos] rmap rmap2 rs2 //=.
  + by move=> [<- _].
  t_xrbindP=> -[rmap1 ?] halloc /= [{}rmap2 ?] hallocs /= <- _.
  move=> hvarsz.
  have := wfr_VARS_ZONE_alloc_lval_call halloc hforall hvarsz.
  by apply: ih hallocs.
Qed.

Lemma wfr_VARS_STATUS_alloc_call_res rmap srs ret_pos rs rmap2 rs2 vars :
  alloc_call_res pmap rmap srs ret_pos rs = ok (rmap2, rs2) ->
  wfr_VARS_STATUS vars rmap ->
  wfr_VARS_STATUS vars rmap2.
Proof.
  elim: rs ret_pos rmap rmap2 rs2 => [|r rs ih] [|oi ret_pos] rmap rmap2 rs2 //=.
  + by move=> [<- _].
  t_xrbindP=> -[rmap1 ?] halloc /= [{}rmap2 ?] hallocs /= <- _.
  move=> hvarss.
  have := wfr_VARS_STATUS_alloc_lval_call halloc hvarss.
  by apply: ih hallocs.
Qed.

Lemma alloc_call_resP table rmap vme m0 s1 s2 srs ret_pos rs rmap2 rs2 vargs1 vargs2 wdb vres1 vres2 s1' :
  valid_state table rmap vme m0 s1 s2 ->
  alloc_call_res pmap rmap srs ret_pos rs = ok (rmap2, rs2) ->
  Forall3 (fun bsr varg1 varg2 => forall (b:bool) (sr:sub_region), bsr = Some (b, sr) ->
    wf_sub_region vme sr (type_of_val varg1) /\
    forall addr, sub_region_addr vme sr = ok addr -> varg2 = Vword addr) (map fst srs) vargs1 vargs2 ->
  List.Forall (fun bsr => forall b sr, bsr = Some (b, sr) -> wf_vars_zone table.(vars) sr.(sr_zone)) (map fst srs) ->
  Forall3 (wf_result vargs1 vargs2) ret_pos vres1 vres2 ->
  Forall3 (value_eq_or_in_mem (emem s2)) ret_pos vres1 vres2 ->
  write_lvals wdb gd s1 rs vres1 = ok s1' ->
  exists s2',
    write_lvals wdb [::] s2 rs2 vres2 = ok s2' /\
    valid_state (foldl remove_binding_lval table rs) rmap2 vme m0 s1' s2'.
Proof.
  move=> hvs halloc haddr hvarsz hresults.
  move hmem: (emem s2) => m2 heqinmems.
  elim: {ret_pos vres1 vres2} hresults heqinmems table rmap s1 s2 hvs haddr hvarsz hmem rs rmap2 rs2 halloc s1'.
  + move=> _ table rmap s1 s2 hvs _ _ _ [|//] _ _ /= [<- <-] _ [<-].
    by eexists; split; first by reflexivity.
  move=> oi vr1 vr2 ret_pos vres1 vres2 hresult _ ih /= /List_Forall3_inv [heqinmem heqinmems]
    table rmap0 s1 s2 hvs haddr hvarsz ? [//|r rs] /=; subst m2.
  t_xrbindP=> _ _ [rmap1 r2] hlval [rmap2 rs2] /= halloc <- <- s1'' s1' hs1' hs1''.
  have [s2' [hs2' hvs']] := alloc_lval_callP hvs hlval haddr hvarsz hresult heqinmem hs1'.
  have heqmem := esym (lv_write_memP (alloc_lval_call_lv_write_mem hlval) hs2').
  move: hvarsz; rewrite -(remove_binding_lval_vars _ r) => hvarsz.
  have [s2'' [hs2'' hvs'']] := ih heqinmems _ _ _ _ hvs' haddr hvarsz heqmem _ _ _ halloc _ hs1''.
  rewrite /= hs2' /= hs2'' /=.
  by eexists; split; first by reflexivity.
Qed.

Lemma check_resultP table rmap vme m0 s1 s2 srs params (sao_return:option nat) res1 res2 wdb vres1 vargs1 vargs2 :
  valid_state table rmap vme m0 s1 s2 ->
  Forall3 (fun osr (x : var_i) v => osr <> None -> subtype x.(vtype) (type_of_val v)) srs params vargs1 ->
  List.Forall2 (fun osr varg2 => forall sr addr,
    osr = Some sr -> sub_region_addr vme sr = ok addr -> varg2 = Vword addr) srs vargs2 ->
  check_result pmap rmap srs params sao_return res1 = ok res2 ->
  get_var wdb (evm s1) res1 = ok vres1 ->
  exists vres2, [/\
    get_var wdb (evm s2) res2 = ok vres2,
    wf_result vargs1 vargs2 sao_return vres1 vres2 &
    value_eq_or_in_mem (emem s2) sao_return vres1 vres2].
Proof.
  move=> hvs hsize haddr hresult hget.
  move: hresult; rewrite /check_result.
  case: sao_return => [i|].
  + case heq: nth => [sr|//].
    t_xrbindP=> /eqP heqty -[sr' _] /get_sub_region_statusP [hsr ->].
    t_xrbindP=> /check_validP hvalid /eqP ? p /get_regptrP hlres1 <-; subst sr'.
    have /wfr_wf hwf := hsr.
    have [addr ok_addr] := wf_sub_region_sub_region_addr hwf.
    have /wfr_ptr := hsr.
    rewrite /get_var /get_local hlres1 => -[? [[<-] /= /(_ _ ok_addr) ->]] /=.
    rewrite orbT /=.
    eexists; split; first by reflexivity.
    + split; last first.
      + symmetry.
        by apply (Forall2_nth haddr None (Vbool true) (nth_not_default heq ltac:(discriminate)) _ _ heq).
      apply (subtype_trans (type_of_get_var hget)).
      rewrite heqty.
      apply (Forall3_nth hsize None res1 (Vbool true) (nth_not_default heq ltac:(discriminate))).
      by rewrite heq.
    eexists; split; first by reflexivity.
    have hget' : get_var true (evm s1) res1 = ok vres1.
    + have /is_sarrP [len hty] := wfr_type (wf_pmap0.(wf_locals) hlres1).
      move: hget; rewrite /get_gvar /= => /get_varP [].
      by rewrite /get_var hty => <- ? /compat_valEl [a] ->.
    have hgvalid := check_gvalid_lvar hsr.
    assert (hval := wfr_val hgvalid hget').
    case: hval => hread hty.
    move=> off w /[dup] /get_val_byte_bound; rewrite hty => hoff.
    apply hread => //.
    by rewrite hvalid.
  t_xrbindP=> /check_varP hlres1 /check_diffP hnnew <-.
  exists vres1; split=> //.
  by have := get_var_kindP hvs hlres1 hnnew hget.
Qed.

Lemma check_resultsP table rmap vme m0 s1 s2 srs params sao_returns res1 res2 vargs1 vargs2 wdb :
  valid_state table rmap vme m0 s1 s2 ->
  Forall3 (fun osr (x : var_i) v => osr <> None -> subtype x.(vtype) (type_of_val v)) srs params vargs1 ->
  List.Forall2 (fun osr varg2 => forall sr addr,
    osr = Some sr -> sub_region_addr vme sr = ok addr -> varg2 = Vword addr) srs vargs2 ->
  check_results pmap rmap srs params sao_returns res1 = ok res2 ->
  forall vres1,
  get_var_is wdb (evm s1) res1 = ok vres1 ->
  exists vres2, [/\
    get_var_is wdb (evm s2) res2 = ok vres2,
    Forall3 (wf_result vargs1 vargs2) sao_returns vres1 vres2 &
    Forall3 (value_eq_or_in_mem (emem s2)) sao_returns vres1 vres2].
Proof.
  move=> hvs hsize haddr.
  rewrite /check_results.
  t_xrbindP=> _.
  elim: sao_returns res1 res2.
  + move=> [|//] _ [<-] _ [<-] /=.
    by eexists; (split; first by reflexivity); constructor.
  move=> sao_return sao_returns ih [//|x1 res1] /=.
  t_xrbindP=> _ x2 hcheck res2 /ih{}ih <-.
  move=> _ v1 hget1 vres1 hgets1 <-.
  have [v2 [hget2 hresult heqinmem]] := check_resultP hvs hsize haddr hcheck hget1.
  have [vres2 [hgets2 hresults heqinmems]] := ih _ hgets1.
  rewrite /= hget2 /= hgets2 /=.
  by eexists; (split; first by reflexivity); constructor.
Qed.

Lemma check_results_alloc_params_not_None rmap srs params sao_returns res1 res2 :
  check_results pmap rmap srs params sao_returns res1 = ok res2 ->
  List.Forall (fun oi => forall i, oi = Some i -> nth None srs i <> None) sao_returns.
Proof.
  rewrite /check_results.
  t_xrbindP=> _.
  elim: sao_returns res1 res2 => //.
  move=> oi sao_returns ih [//|x1 res1] /=.
  t_xrbindP => _ x2 hresult res2 /ih{}ih _.
  constructor=> //.
  move=> i ?; subst oi.
  move: hresult => /=.
  by case: nth.
Qed.

(* If we write (in the target) in a reg that is distinct from everything else,
  then we preserve [valid_state]. This is applied only to [vxlen] for now, so it
  seems a bit overkill to have a dedicated lemma.
*)
Lemma valid_state_distinct_reg table rmap vme m0 s1 s2 x v :
  valid_state table rmap vme m0 s1 s2 ->
  x <> pmap.(vrip) ->
  x <> pmap.(vrsp) ->
  Sv.In x pmap.(vnew) ->
  (forall y p, get_local pmap y = Some (Pregptr p) -> x <> p) ->
  valid_state table rmap vme m0 s1 (with_vm s2 (evm s2).[x <- v]).
Proof.
  move=> hvs hnrip hnrsp hnew hneq.
  case:(hvs) => hscs hvalid hdisj hincl hincl2 hunch hrip hrsp heqvm hwft hwfr heqmem hglobv htop.
  constructor=> //=.
  + by rewrite Vm.setP_neq //; apply /eqP.
  + by rewrite Vm.setP_neq //; apply /eqP.
  + by move=> y ??; rewrite Vm.setP_neq; [auto|apply/eqP;congruence].
  case: (hwfr) => hwfsr hwfst hvarsz hvarss hval hptr; split=> //.
  move=> y sry /hptr [pky [hly hpk]].
  rewrite hly.
  eexists; split; first by reflexivity.
  case: pky hly hpk => //= p hly hgetp.
  rewrite Vm.setP_neq //; apply/eqP.
  by apply: hneq hly.
Qed.

Lemma fill_fill_mem table rmap vme m0 s1 s2 sr len addr l a :
  valid_state table rmap vme m0 s1 s2 ->
  wf_sub_region vme sr (sarr len) ->
  sub_region_addr vme sr = ok addr ->
  WArray.fill len l = ok a ->
  exists m2, fill_mem (emem s2) addr l = ok m2.
Proof.
  move=> hvs hwf ok_addr.
  rewrite /WArray.fill /fill_mem.
  t_xrbindP=> /eqP hsize [i {}a] /= hfold _.

  have hvp: forall k, 0 <= k < len -> validw (emem s2) Aligned (addr + wrepr _ k)%R U8.
  + move=> k hk.
    apply (validw_sub_region_addr_ofs hvs hwf ok_addr).
    + by rewrite wsize8 /=; lia.
    by apply is_align8.

  elim: l (emem s2) hvp 0 (WArray.empty len) {hsize} hfold => [|w l ih] m2 hvp z a0 /=.
  + by move=> _; eexists.
  t_xrbindP=> _ a' hset <- /ih{}ih.
  move: hset => /WArray.set_bound; rewrite WArray.mk_scale_U8 Z.mul_1_r wsize8 => -[h1 h2 _].
  have hvp2: validw m2 Aligned (addr + wrepr _ z)%R U8.
  + by apply hvp; lia.
  have /writeV -/(_ w) [m2' hm2'] := hvp2.
  rewrite addE hm2' /=.
  apply ih.
  by move=> k hk; rewrite (write_validw_eq hm2'); apply hvp.
Qed.

(* If we update the [scs] component identically in the source and the target,
   then [valid_state] is preserved. *)
Lemma valid_state_scs table rmap vme m0 s1 s2 scs :
  valid_state table rmap vme m0 s1 s2 ->
  valid_state table rmap vme m0 (with_scs s1 scs) (with_scs s2 scs).
Proof.
  move=> hvs.
  case:(hvs) => hscs hvalid hdisj hincl hincl2 hunch hrip hrsp heqvm hwft hwfr heqmem hglobv htop.
  constructor=> //=.
  case: (hwfr) => hwfsr hwfst hval hptr.
  by split.
Qed.

Lemma Incl_set_clear_pure rmap sr :
  Incl (set_clear_pure rmap sr) rmap.
Proof.
  split => //=.
  move=> r y.
  rewrite get_var_status_set_clear_status.
  case: eq_op => /=.
  + by apply incl_clear_status_map_aux.
  by apply incl_status_refl.
Qed.

Lemma add_sub_interval_idempotent i1 s i2 :
  add_sub_interval i1 s = Some i2 ->
  add_sub_interval i2 s = Some i2.
Proof.
  elim: i1 i2 => [|s1 i1 ih1] i2 /=.
  + move=> [<-] /=.
    by rewrite eq_refl.
  case: ifP => heq.
  + move=> [<-] /=.
    by rewrite heq.
  case hle1: (odflt _ _).
  + move=> [<-] /=.
    by rewrite eq_refl.
  case hle2: (odflt _ _) => //.
  apply: obindP => {}i2 /ih1 hadd [<-] /=.
  by rewrite heq hle1 hle2 hadd.
Qed.

Lemma incl_status_clear_status_idempotent status z :
  incl_status
    (odflt Unknown (clear_status status z))
    (odflt Unknown (clear_status (odflt Unknown (clear_status status z)) z)).
Proof.
  case: z => [//|s _] /=.
  case: status => [||i] /=.
  + by rewrite eq_refl /= mem_head.
  + by [].
  case hadd: add_sub_interval => [i'|//] /=.
  rewrite (add_sub_interval_idempotent hadd) /=.
  by apply incl_interval_refl.
Qed.

Lemma incl_status_clear_status_map_aux_idempotent rmap z x status :
  incl_status
    (odflt Unknown (clear_status_map_aux rmap z x status))
    (odflt Unknown (clear_status_map_aux rmap z x
      (odflt Unknown (clear_status_map_aux rmap z x status)))).
Proof.
  rewrite /clear_status_map_aux.
  case: (let%opt _ := _ in get_suffix _ _) => [oz|//] /=.
  case: oz => [z'|] /=; last by apply incl_status_refl.
  by apply incl_status_clear_status_idempotent.
Qed.

Lemma Incl_set_clear_pure_idempotent rmap sr :
  Incl (set_clear_pure rmap sr) (set_clear_pure (set_clear_pure rmap sr) sr).
Proof.
  split=> //.
  move=> ry y.
  rewrite /= !get_var_status_set_clear_status.
  case: eqP => _ /=; last by apply incl_status_refl.
  rewrite /clear_status_map_aux /=.
  by apply incl_status_clear_status_map_aux_idempotent.
Qed.

Lemma wfr_VARS_ZONE_alloc_syscall ii rmap rs o es rmap2 c vars :
  alloc_syscall saparams pmap ii rmap rs o es = ok (rmap2, c) ->
  wfr_VARS_ZONE vars rmap ->
  wfr_VARS_ZONE vars rmap2.
Proof.
  rewrite /alloc_syscall => /add_iinfoP.
  case: o => [len].
  t_xrbindP=> _.
  case: rs => // -[] // x [] //.
  case: es => // -[] // g [] //.
  t_xrbindP=> _ _ _ _ srg /get_sub_regionP hsrg _ /set_clearP [_ ->] <- _.
  move=> hvarsz1.
  apply wfr_VARS_ZONE_set_move => //.
  by apply (hvarsz1 _ _ hsrg).
Qed.

Lemma wfr_VARS_STATUS_alloc_syscall ii rmap rs o es rmap2 c vars :
  alloc_syscall saparams pmap ii rmap rs o es = ok (rmap2, c) ->
  wfr_VARS_ZONE vars rmap ->
  wfr_VARS_STATUS vars rmap ->
  wfr_VARS_STATUS vars rmap2.
Proof.
  rewrite /alloc_syscall => /add_iinfoP.
  case: o => [len].
  t_xrbindP=> _.
  case: rs => // -[] // x [] //.
  case: es => // -[] // g [] //.
  t_xrbindP=> _ _ _ _ srg /get_sub_regionP hsrg _ /set_clearP [_ ->] <- _.
  move=> hvarsz1 hvarss1 /=.
  apply wfr_VARS_STATUS_set_move_status => //.
  apply wfr_VARS_STATUS_set_clear_status => //.
  by apply (hvarsz1 _ _ hsrg).
Qed.


(* TODO: in the long term, try to merge with what is proved about calls *)
Lemma alloc_syscallP ii rmap rs o es rmap2 c table vme m0 s1 s2 ves scs m vs s1' :
  alloc_syscall saparams pmap ii rmap rs o es = ok (rmap2, c) ->
  valid_state table rmap vme m0 s1 s2 ->
  sem_pexprs true gd s1 es = ok ves ->
  exec_syscall_u (escs s1) (emem s1) o ves = ok (scs, m, vs) ->
  write_lvals true gd (with_scs (with_mem s1 m) scs) rs vs = ok s1' ->
  exists s2',
    sem P' rip s2 c s2' /\
    valid_state (foldl remove_binding_lval table rs) rmap2 vme m0 s1' s2'.
Proof.
  move=> halloc hvs.
  move: halloc; rewrite /alloc_syscall; move=> /add_iinfoP.
  case: o => [len].
  t_xrbindP=> /ZltP hlen.
  case: rs => // -[] // x [] //.
  case: es => // -[] // g [] //.
  t_xrbindP=> pg /get_regptrP hlg px /get_regptrP hlx srg /get_sub_regionP hsrg {}rmap2 hrmap2 <- <-{c}.
  rewrite /= /exec_getrandom_u /=.
  t_xrbindP=> vg hgvarg <-{ves} [_ _] ag' /to_arrI ?
    a2 hfill [<- <-] <-{scs} <-{m} <-{vs} /=; subst vg.
  t_xrbindP=> {}s1' /write_varP + <- => -[-> hdb h].
  have /wf_locals /= hlocal := hlx.
  have /vm_truncate_valE [hty htreq]:= h.
  set i1 := (X in [:: X; _]).
  set i2 := (X in [:: _; X]).

  (* write [len] in register [vxlen] *)
  have := @sap_immediateP _ hsaparams P' rip s2 (with_var (gv g) (vxlen pmap)) len (@wt_len wf_pmap0).
  set s2' := with_vm s2 _ => hsem1.
  have hvs': valid_state table rmap vme m0 s1 s2'.
  + apply (valid_state_distinct_reg _ hvs).
    + by apply len_neq_rip.
    + by apply len_neq_rsp.
    + by apply len_in_new.
    by move=> y p; apply len_neq_ptr.

  have hwfg: wf_sub_region vme srg g.(gv).(vtype).
  + by apply (wfr_wf hsrg).
  have srg_vars: wf_vars_zone table.(vars) srg.(sr_zone).
  + by apply (wfr_vars_zone hsrg).

  (* clear the argument *)
  have hincl: Incl rmap2 rmap.
  + move /set_clearP : hrmap2 => [_ ->].
    by apply Incl_set_clear_pure.
  have hwfst: wfr_STATUS rmap2 vme.
  + move /set_clearP : hrmap2 => [_ ->] /=.
    by apply (wfr_STATUS_set_clear_status wfr_wf hwfg wfr_status).
  have hvarss: wfr_VARS_STATUS table.(vars) rmap2.
  + move /set_clearP : hrmap2 => [_ ->].
    by apply (wfr_VARS_STATUS_set_clear_status wfr_vars_zone srg_vars wfr_vars_status).
  have hvs2 := valid_state_Incl hincl hwfst hvarss hvs'.

  (* write the randombytes in memory (in the target) *)
  move: hwfg; rewrite (type_of_get_gvar_array hgvarg) => hwfg.
  have [addrg ok_addrg] := wf_sub_region_sub_region_addr hwfg.
  have [m2 hfillm] := fill_fill_mem hvs hwfg ok_addrg hfill.
  have hvs2': valid_state table rmap2 vme m0 s1 (with_mem s2' m2).
  + rewrite -(with_mem_same s1).
    apply (valid_state_holed_rmap
            (l:=[::(srg, sarr len)])
            hvs2 (λ _ _ _, erefl) (fill_mem_stack_stable hfillm)
            (fill_mem_validw_eq hfillm)).
    + move=> p hvalid.
      rewrite (fill_mem_disjoint hfillm); first by apply vs_eq_mem.
      rewrite -(WArray.fill_size hfill) positive_nat_Z.
      apply (disjoint_zrange_incl_l (zbetween_sub_region_addr hwfg ok_addrg)).
      apply vs_disjoint => //.
      by apply hwfg.(wfr_slot).
    + constructor; last by constructor.
      split=> //.
      by move: hrmap2 => /set_clearP [? _].
    + move=> p hvalid1 hvalid2 /List_Forall_inv [/(_ _ ok_addrg) hdisj _].
      rewrite (fill_mem_disjoint hfillm) //.
      by rewrite -(WArray.fill_size hfill) positive_nat_Z.
    constructor; last by constructor.
    have /set_clearP [_ ->] /= := hrmap2.
    by apply (set_clear_pure_sub_region_cleared wfr_wf wfr_status hwfg).

  (* update the [scs] component *)
  set s1'' := with_scs s1 (get_random (escs s1) len).1.
  set s2'' := with_scs (with_mem s2' m2) (get_random (escs s1) len).1.
  have hvs2'': valid_state table rmap2 vme m0 s1'' s2''.
  + by apply valid_state_scs.

  (* write the result *)
  set s1''' := with_vm s1'' (evm s1'').[x <- Varr a2].
  set s2''' := with_vm s2'' (evm s2'').[px <- Vword addrg].
  have hvs2''': valid_state (remove_binding table x) (set_move rmap2 x srg Valid) vme m0 s1''' s2'''.
  + rewrite /s1''' /s2'''.
    move: hwfg; rewrite -hty => hwfg.
    apply: (valid_state_set_move_regptr hvs2'' hwfg ok_addrg _ srg_vars _ hlx h) => //.
    rewrite htreq; split=> // off addrg' w ok_addrg' off_valid /[dup] /get_val_byte_bound /= hoff.
    move: ok_addrg'; rewrite ok_addrg => -[?]; subst addrg'.
    rewrite (WArray.fill_get8 hfill) (fill_mem_read8_no_overflow _ hfillm)
            -?(WArray.fill_size hfill) ?positive_nat_Z /=;
      try lia.
    by case: andb.

  (* wrap up *)
  exists s2'''; split=> //.
  apply (Eseq (s2 := s2')) => //.
  apply sem_seq1; constructor.
  apply: Esyscall.
  + rewrite /= /get_gvar /= /get_var.
    have /wfr_ptr := hsrg; rewrite /get_local hlg => -[_ [[<-] /= hpk]].
    rewrite (hpk _ ok_addrg) /=.
    by rewrite Vm.setP_eq wt_len vm_truncate_val_eq //; eauto.
  + rewrite /= /exec_syscall_s /= !truncate_word_u /=.
    rewrite /exec_getrandom_s_core wunsigned_repr_small; last by lia.
    by rewrite -vs_scs hfillm.
  by rewrite /= LetK; apply write_var_eq_type; rewrite // hlocal.(wfr_rtype).
Qed.

End WITH_PARAMS.
