(* ** Imports and settings *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype ssralg.

Require Import
  pseudo_operator
  sem_type
  shift_kind
  strings
  slh_ops
  sopn_semi
  type
  values
  var.

Local Unset Elimination Schemes.

(* ----------------------------------------------------------------------------- *)
Variant arg_constrained_register :=
| ACR_any
| ACR_exact of var
| ACR_subset of seq var
.

Variant arg_desc :=
| ADImplicit  of var
| ADExplicit  of nat & arg_constrained_register.

Variant arg_position :=
| APout of nat
| APin of nat.

(* -------------------------------------------------------------------- *)
(* Flag indicating if the instruction has data operand independent timing *)
Variant doit_t :=
  | DOIT
  | NOT_DOIT.

Record instruction_desc := mkInstruction {
  str      : unit -> string;
  tin      : list atype;
  i_in     : seq arg_desc;
  tout     : list atype;
  i_out    : seq arg_desc;
  conflicts: seq (arg_position * arg_position);
  (* Total semantics: no error can be raised and the boolean outputs are plain
     booleans (no [None]); the semantics of the instruction is obtained from it
     by [mk_semi], see [semi] below. *)
  i_semi_total : sem_prod (map eval_atype tin) (sem_tuple_t (map eval_atype tout));
  (* This field allows to ensure the validity of the instruction,
     it is usefull when the its name allows to encode more instructions than the real existing one.
     See field id_valid in arch/arch_decl.v
  *)
  i_valid  : bool;
  i_safe   : seq safety_cond;
  (* The error raised when one of the safety conditions does not hold. *)
  i_err    : error;
  (* One initialisation condition per output: the output is defined exactly
     when its condition holds on the arguments. *)
  i_init   : seq safety_cond;
  (* Whether the operator has data operand independent timing, i.e. it is
     implemented using only DOIT (Intel) / DIT (ARM) instructions.
     See field id_doit in arch/arch_decl.v.
     Pseudo operators and SLH operators are compiled to DOIT instructions
     only, but this needs to be checked manually. *)
  i_doit   : doit_t;
  (* Extra properties ensuring that previous information are consistent:
     the safety and initialisation conditions are well formed, there is one
     initialisation condition per output, and the error is not a type error *)
  i_wf         : [&& all (safety_cond_wf (map eval_atype tin)) i_safe,
                     all (safety_cond_wf (map eval_atype tin)) i_init,
                     ssrnat.eqn (size i_init) (size tout) & ~~ is_ErrType i_err];
    (* the semantics is monotone with respect to [value_uincl] *)
  semu     : forall vs vs' v,
                values_uincl vs vs' ->
                app_sopn_v (mk_semi i_safe i_err i_init i_semi_total) vs = ok v ->
                exists2 v', app_sopn_v (mk_semi i_safe i_err i_init i_semi_total) vs' = ok v'
                  & values_uincl v v';
}.

(* The semantics of an instruction: the safety conditions are checked on the
   arguments, then the total semantics is filtered by the initialisation
   conditions. *)
Definition semi (i : instruction_desc) :
    sem_prod (map eval_atype i.(tin)) (exec (sem_tuple (map eval_atype i.(tout)))) :=
  mk_semi i.(i_safe) i.(i_err) i.(i_init) i.(i_semi_total).

Arguments semu _ [vs vs' v] _ _.

(* Transport of the monotony along an extensional equality of semantics. *)
Lemma semu_eq tin tout (f g : sem_prod tin (exec (sem_tuple tout))) :
  sem_prod_eq tin f g ->
  (forall vs vs' v, values_uincl vs vs' -> app_sopn_v f vs = ok v ->
     exists2 v', app_sopn_v f vs' = ok v' & values_uincl v v') ->
  forall vs vs' v, values_uincl vs vs' -> app_sopn_v g vs = ok v ->
     exists2 v', app_sopn_v g vs' = ok v' & values_uincl v v'.
Proof.
  move=> heq h vs vs' v hu; rewrite -(sem_prod_eq_app_sopn_v vs heq).
  by move=> /(h _ _ _ hu) [v' ]; rewrite (sem_prod_eq_app_sopn_v vs' heq); exists v'.
Qed.

Notation mk_instr_desc str tin i_in tout i_out semi_total safe err init valid doit :=
  {| str          := str;
     tin          := tin;
     i_in         := i_in;
     tout         := tout;
     i_out        := i_out;
     conflicts    := [::];
     i_semi_total := semi_total;
     i_safe       := safe;
     i_err        := err;
     i_init       := init;
     i_valid      := valid;
     i_doit       := doit;
     i_wf         := refl_equal;
     semu         := @vuincl_app_sopn_v (map eval_atype tin) (map eval_atype tout)
                       (@mk_semi (map eval_atype tin) (map eval_atype tout)
                          safe err init semi_total) refl_equal;
  |}.

(* For an instruction without safety condition. *)
Notation mk_instr_desc_safe str tin i_in tout i_out semi_total init valid doit :=
  (mk_instr_desc str tin i_in tout i_out semi_total [::] ErrArith init valid doit)
  (only parsing).

(* -------------------------------------------------------------------- *)

Variant prim_x86_suffix :=
  | PVp of wsize
  | PVs of signedness & wsize
  | PVv of velem & wsize
  | PVsv of signedness & velem & wsize
  | PVx of wsize & wsize
  | PVvv of velem & wsize & velem & wsize
.

Variant prim_constructor (asm_op:Type) :=
  | PrimX86 of seq prim_x86_suffix & (prim_x86_suffix -> option asm_op)
  | PrimARM of
    (bool                 (* set_flags *)
     -> bool              (* is_conditional *)
     -> result string asm_op).

Class asmOp (asm_op : Type) := {
  _eqT           : eqTypeC asm_op
  ; asm_op_instr : asm_op -> instruction_desc
  ; prim_string   : list (string * prim_constructor asm_op)
}.

#[global]
Existing Instance _eqT.

Definition asm_op_t {asm_op} {asmop : asmOp asm_op} := asm_op.

Section WITH_PARAMS.

Context
  {asm_op : Type}
  {pd : PointerData}
  {msfsz : MSFsize}
  {asmop : asmOp asm_op}.

Variant sopn :=
| Opseudo_op of pseudo_operator
| Oslh of slh_op
| Oasm of asm_op_t.

Definition sopn_beq (o1 o2:sopn) :=
  match o1, o2 with
  | Opseudo_op o1, Opseudo_op o2 => o1 == o2
  | Oslh o1, Oslh o2 => o1 == o2
  | Oasm o1, Oasm o2 => o1 == o2 ::>
  | _, _ => false
  end.

Lemma sopn_eq_axiom : Equality.axiom sopn_beq.
Proof.
  move=> [] ? [] ?.
  all: by [ constructor | apply: reflect_inj eqP => ?? [] ].
Qed.

HB.instance Definition _ := hasDecEq.Build sopn sopn_eq_axiom.

Definition sopn_copy (ws : wsize) (len : Z) : sopn :=
  Opseudo_op (Ocopy ws len).
Definition sopn_nop : sopn := Opseudo_op Onop.
Definition sopn_mulu (ws : wsize) : sopn := Opseudo_op (Omulu ws).
Definition sopn_addcarry (ws : wsize) : sopn := Opseudo_op (Oaddcarry ws).
Definition sopn_subcarry (ws : wsize) : sopn := Opseudo_op (Osubcarry ws).

Definition is_Oslh (op : sopn) : option slh_op :=
  if op is Oslh op then Some op else None.

Lemma is_OslhP op : is_reflect Oslh op (is_Oslh op).
Proof. case: op; by constructor. Qed.

Definition is_spill_op o :=
  if o is Opseudo_op (Ospill o tys) then Some (o, tys)
  else None.

Lemma is_spill_opP o s tys :
  is_spill_op o = Some (s, tys) ->
  o = Opseudo_op (Ospill s tys).
Proof. by case: o => // -[] // ?? [-> ->]. Qed.

(* ------------------------------------------------------------- *)
(* Descriptors for speudo operators                              *)

(* The fields [i_in] and [i_out] are used in the regalloc pass only. The
   following instructions should be replaced before that pass (in lowering),
   thus we do not need to set those fields to true values. We respect the number
   of in- and out- arguments, but apart from that, we give some trivial values.
*)

Local Notation E n := (ADExplicit n ACR_any).

(* A total counterpart of [WArray.copy]: it performs exactly the same writes,
   but reads an uninitialised cell as 0. On the safe domain (every read of the
   source succeeds) both compute the same array. It is [WArray.copy] in the
   total mode ([copy_totalE]), as a bare value, which is what [mk_semi]
   expects. *)

Definition copy_get ws {len} (a : WArray.array len) (i : Z) : word ws :=
  if WArray.get (sm := total) Unaligned AAscale ws a i is Ok w then w else 0%R.

Definition copy_set {ws len} (t : WArray.array len) (i : Z) (w : word ws) :
    WArray.array len :=
  if WArray.set (sm := total) t Unaligned AAscale i w is Ok t' then t' else t.

Definition copy_total ws {n} (a : WArray.array (arr_size ws n)) :
    WArray.array (arr_size ws n) :=
  foldl (fun t i => copy_set t i (copy_get ws a i)) (WArray.empty (arr_size ws n))
    (ziota 0 n).

Arguments copy_get ws {len} a i.
Arguments copy_set {ws len} t i w.
Arguments copy_total ws {n} a.

(* [copy_total] is [WArray.copy] in the total mode, which never fails. *)
Lemma copy_totalE ws n (a : WArray.array (arr_size ws n)) :
  @WArray.copy total ws n a = ok (copy_total ws a).
Proof.
rewrite /WArray.copy /WArray.fcopy /copy_total.
elim: (ziota 0 n) (WArray.empty (arr_size ws n)) => //= i l ih t.
rewrite /copy_get /copy_set.
have hg : is_ok (WArray.get (sm := total) Unaligned AAscale ws a i) by apply: read_total_ok.
move: hg; case: (WArray.get (sm := total) Unaligned AAscale ws a i) => [w | //] _ /=.
have hs : is_ok (WArray.set (sm := total) t Unaligned AAscale i w) by apply: write_total_ok.
move: hs; case: (WArray.set (sm := total) t Unaligned AAscale i w) => [t' | //] _ /=.
exact: ih.
Qed.

(* On a cell that is in bounds, the only possible failure of a read is an
   uninitialised cell. *)
Lemma get8_errE len (a : WArray.array len) i e :
  WArray.in_bound a i -> WArray.get8 partial a i = Error e -> e = ErrAddrUndef.
Proof. by rewrite WArray.get8_partial => -> /=; case: WArray.is_init => //= -[<-]. Qed.

Lemma mapM_get8_errE len (a : WArray.array len) (f : Z -> Z) l e :
  all (fun k => WArray.in_bound a (f k)) l ->
  mapM (fun k => WArray.get8 partial a (f k)) l = Error e -> e = ErrAddrUndef.
Proof.
elim: l e => //= k l ih e /andP [hk hl].
case hg: WArray.get8 => [w|e'] /=; last by move=> [<-]; apply: get8_errE hg.
by case hm: mapM => [?|e2] //= [?]; subst e2; apply: ih hl hm.
Qed.

Lemma get_errE ws len (a : WArray.array len) i e :
  validw a Unaligned (i * mk_scale AAscale ws)%Z ws ->
  WArray.get Unaligned AAscale ws a i = Error e -> e = ErrAddrUndef.
Proof.
rewrite /validw => /andP [] _ hv.
rewrite /WArray.get /CoreMem.read /is_aligned_if.
case hm: mapM => [l|e'] //= [<-].
apply: mapM_get8_errE hm; exact: hv.
Qed.

Lemma copy_validw ws n (a : WArray.array (arr_size ws n)) i :
  (0 <= i < n)%Z -> validw a Unaligned (i * mk_scale AAscale ws)%Z ws.
Proof.
move=> hi; rewrite /validw /is_aligned_if andTb.
apply ziota_ind => //= k ? hk ->; rewrite andbT; apply/WArray.in_boundP.
by rewrite WArray.addE arr_sizeE; Lia.nia.
Qed.

Lemma fcopy_eq ws n (a : WArray.array (arr_size ws n)) l
    (t : WArray.array (arr_size ws n)) :
  all (fun i => (0 <=? i)%Z && (i <? n)%Z) l ->
  foldM (fun i t => Let w := WArray.get Unaligned AAscale ws a i in
                    WArray.set t Unaligned AAscale i w) t l
  = (if all (fun i => is_ok (WArray.get Unaligned AAscale ws a i)) l
     then ok (foldl (fun t i => copy_set t i (copy_get ws a i)) t l)
     else Error ErrAddrUndef).
Proof.
elim: l t => //= i l ih t /andP [] /andP [] /ZleP h1 /ZltP h2 hl.
have hv := @copy_validw ws n t i (conj h1 h2).
have hva := @copy_validw ws n a i (conj h1 h2).
case hg : (WArray.get Unaligned AAscale ws a i) => [w | e] /=; last first.
+ by rewrite (@get_errE _ _ _ _ _ hva hg).
have [t' ht'] : exists t', WArray.set t Unaligned AAscale i w = ok t'.
+ by apply: (writeV (CM:= WArray.array_CM (arr_size ws n))).
have hgt : WArray.get (sm := total) Unaligned AAscale ws a i = ok w.
+ by case/read_partialE: hg.
have ht't : WArray.set (sm := total) t Unaligned AAscale i w = ok t'.
+ by case/write_partialE: ht'.
rewrite ht' /= /copy_set /copy_get hgt ht't /=.
by apply ih.
Qed.

(* [copy] fails exactly when one of the cells it reads is uninitialised, that
   is, exactly when its safety condition does not hold. *)
Lemma array_copy_eq ws n (a : WArray.array (arr_size ws n)) :
  @WArray.copy partial ws n a =
  (if all (fun i => is_ok (WArray.get Unaligned AAscale ws a i)) (ziota 0 n)
   then ok (copy_total ws a) else Error ErrAddrUndef).
Proof.
rewrite /WArray.copy /WArray.fcopy /copy_total; apply fcopy_eq.
apply ziota_ind => //= i l hi ->; rewrite andbT.
by apply/andP; split; [apply/ZleP | apply/ZltP]; Lia.lia.
Qed.

Lemma array_copy_semi_eq ws p :
  sem_prod_eq [:: carr (arr_size ws p)] (@WArray.copy partial ws p)
    (@mk_semi [:: carr (arr_size ws p)] [:: carr (arr_size ws p)]
       [:: sc_all_init ws p 0] ErrAddrUndef [:: IBool true] (@copy_total ws p)).
Proof.
move=> t.
have -> : @mk_semi [:: carr (arr_size ws p)] [:: carr (arr_size ws p)]
            [:: sc_all_init ws p 0] ErrAddrUndef [:: IBool true] (@copy_total ws p) t
        = (Let _ := check_safe [:: Varr t] [:: sc_all_init ws p 0] ErrAddrUndef in
           ok (copy_total ws t)) by [].
rewrite /check_safe /= andbT (safety_cond_holds_all_init (t := t)) //= array_copy_eq.
by case: all.
Qed.

(* Reading the array is the only condition, and the output is always
   defined. *)
Lemma copy_wf ws p :
  [&& all (safety_cond_wf (map eval_atype [:: aarr ws p])) [:: sc_all_init ws p 0],
      all (safety_cond_wf (map eval_atype [:: aarr ws p])) [:: IBool true],
      ssrnat.eqn (size [:: IBool true]) (size [:: aarr ws p])
    & ~~ is_ErrType ErrAddrUndef].
Proof. by rewrite /= andbT safety_cond_wf_all_init. Qed.

Definition Ocopy_instr ws p :=
  {| str      := pp_sz "copy" ws;
     tin      := [:: aarr ws p];
     i_in     := [:: E 1];
     tout     := [:: aarr ws p];
     i_out    := [:: E 0];
     conflicts:= [::];
     i_semi_total := @copy_total ws p;
     i_valid  := true;
     i_doit   := DOIT;
     i_safe   := [:: sc_all_init ws p 0];
     i_err    := ErrAddrUndef;
     i_init   := [:: IBool true];
     i_wf         := copy_wf ws p;
     semu     := semu_eq (tin := [:: carr (arr_size ws p)]) (tout := [:: carr (arr_size ws p)])
                  (@array_copy_semi_eq ws p) (@vuincl_copy ws p);
  |}.

Definition declassify_semi ty : sem_prod [:: ty ] (exec (sem_tuple [::])) := fun=> ok tt.
Arguments declassify_semi _ : clear implicits.

Lemma declassify_semu ty vs vs' u:
  values_uincl vs vs' ->
  app_sopn_v (declassify_semi ty) vs = ok u ->
  exists2 u', app_sopn_v (declassify_semi ty) vs' = ok u' & values_uincl u u'.
Proof.
  rewrite /app_sopn_v.
  case: vs => // v /=; t_xrbindP => - [] // /List_Forall2_inv_l[] v' [] _ [] -> [] v_v' /List_Forall2_inv_l -> [] t ok_t hsem <-.
  have [ t' ok_t' t_t' ] := val_uincl_of_val v_v' ok_t.
  exists [::]; last by [].
  by rewrite ok_t'.
Qed.

Definition Odeclassify_instr ty :=
  let cty := eval_atype ty in
  {| str      := pp_s (string_of_pseudo_operator (Odeclassify ty));
    tin      := [:: ty ];
    i_in     := [:: E 0 ];
    tout     := [:: ];
    i_out    := [:: ];
    conflicts:= [::];
    i_semi_total := fun=> tt;
    i_safe   := [:: ];
    i_err    := ErrArith;
    i_init   := [:: ];
    i_valid  := true;
    i_doit   := DOIT;
    i_wf         := refl_equal;
    semu     := semu_eq (tin := [:: cty ]) (tout := [::]) (fun _ => erefl) (@declassify_semu cty);
  |}.

Definition Odeclassify_mem_instr len :=
  let ty := aword Uptr in
  let cty := eval_atype ty in
  {| str      := pp_s (string_of_pseudo_operator (Odeclassify_mem len));
    tin      := [:: ty ];
    i_in     := [:: E 0 ];
    tout     := [:: ];
    i_out    := [:: ];
    conflicts:= [::];
    i_semi_total := fun=> tt;
    i_safe   := [:: ];
    i_err    := ErrArith;
    i_init   := [:: ];
    i_valid  := true;
    i_doit   := DOIT;
    i_wf         := refl_equal;
    semu     := semu_eq (tin := [:: cty ]) (tout := [::]) (fun _ => erefl) (@declassify_semu cty);
  |}.

Definition Onop_instr :=
  mk_instr_desc_safe (pp_s "NOP")
           [::] [::]
           [::] [::]
           tt [::] true DOIT.

Definition Omulu_instr sz :=
  mk_instr_desc_safe (pp_sz "mulu" sz)
           [:: aword sz; aword sz]
           [:: E 0; E 1] (* this info is irrelevant *)
           [:: aword sz; aword sz]
           [:: E 2; E 3] (* this info is irrelevant *)
           (@wumul sz)
           [:: IBool true; IBool true] true DOIT.

Definition Oaddcarry_instr sz :=
  mk_instr_desc_safe (pp_sz "adc" sz)
           [:: aword sz; aword sz; abool]
           [:: E 0; E 1; E 2] (* this info is irrelevant *)
           [:: abool; aword sz]
           [:: E 3; E 4]      (* this info is irrelevant *)
           (@waddcarry sz)
           [:: IBool true; IBool true] true DOIT.

Definition Osubcarry_instr sz :=
  mk_instr_desc_safe (pp_sz "sbb" sz)
           [:: aword sz; aword sz; abool]
           [:: E 0; E 1; E 2] (* this info is irrelevant *)
           [:: abool; aword sz]
           [:: E 3; E 4]      (* this info is irrelevant *)
           (@wsubcarry sz)
           [:: IBool true; IBool true] true DOIT.

Fixpoint spill_semi (tys: seq ctype) : sem_prod tys (sem_tuple [::]):=
  match tys as tys0 return sem_prod tys0 (sem_tuple [::]) with
  | [::] => tt
  | t::tys => fun (_ : sem_t t) => spill_semi tys
  end.

Lemma spill_semu tys (vs vs' : seq value) (v : values) :
   values_uincl vs vs' ->
   app_sopn_v (sem_prod_ok tys (spill_semi tys)) vs = ok v ->
   exists2 v' : values, app_sopn_v (sem_prod_ok tys (spill_semi tys)) vs' = ok v' &
                        values_uincl v v'.
Proof.
  rewrite /app_sopn_v; elim: tys vs vs' v => /= [ | t tys hrec] ?? v; case => //=.
  + by move=> [<-]; exists [::].
  move=> v1 v1' vs vs' huv hu /=; t_xrbindP => ?? hv ha <-.
  have [? -> _ /=]:= val_uincl_of_val huv hv.
  by apply: hrec;[ apply hu | rewrite ha].
Qed.

Lemma spill_semi_eq tys :
  sem_prod_eq tys (sem_prod_ok tys (spill_semi tys))
    (@mk_semi tys [::] [::] ErrArith [::] (spill_semi tys)).
Proof. rewrite /mk_semi; elim: tys (@nil value) => //= t tys ih vs v; apply ih. Qed.

Definition Ospill_instr o (tys:seq atype) :=
  let ctys := map eval_atype tys in
  let semi := spill_semi ctys in
  {| str      := (fun _ => string_of_pseudo_operator (Ospill o tys));
     tin      := tys;
     i_in     := mapi (fun i _ => E i) tys;
     tout     := [:: ];
     i_out    := [:: ];
     conflicts:= [::];
     i_semi_total := semi;
     i_safe   := [:: ];
     i_err    := ErrArith;
     i_init   := [:: ];
     i_valid  := true;
     i_doit   := DOIT;
     i_wf         := refl_equal;
     semu     := semu_eq (tin := ctys) (tout := [::]) (@spill_semi_eq ctys) (@spill_semu ctys);
  |}.

Lemma swap_semi_eq t :
  sem_prod_eq [:: t; t] (sem_prod_ok [:: t; t] (@swap_semi t))
    (@mk_semi [:: t; t] [:: t; t] [::] ErrArith [:: IBool true; IBool true]
       (fun x y => (y, x))).
Proof. by move=> x y; rewrite /mk_semi /= /swap_semi /= !filter_ot_true. Qed.

Definition Oswap_instr ty :=
  let cty := eval_atype ty in
  let ctys := [:: cty; cty] in
  let semi := @swap_semi cty in
  {| str    := (fun _ => "swap"%string);
     tin    := [:: ty; ty];
     i_in   := [:: E 0; E 1]; (* this info is relevant *)
     tout   := [:: ty; ty];
     i_out  := [:: E 0; E 1]; (* this info is relevant *)
     conflicts:= [::];
     i_semi_total := fun x y => (y, x);
     i_safe := [::];
     i_err  := ErrArith;
     i_init := [:: IBool true; IBool true];
     i_valid := true;
     i_doit := DOIT;
     i_wf         := refl_equal;
     semu   := semu_eq (tin := ctys) (tout := ctys) (@swap_semi_eq cty) (@swap_semu cty);
  |}.

Definition pseudo_op_get_instr_desc (o : pseudo_operator) : instruction_desc :=
  match o with
  | Ospill o tys => Ospill_instr o tys
  | Ocopy ws n   => Ocopy_instr ws n
  | Odeclassify t=> Odeclassify_instr t
  | Odeclassify_mem len => Odeclassify_mem_instr len
  | Onop         => Onop_instr
  | Omulu     sz => Omulu_instr sz
  | Oaddcarry sz => Oaddcarry_instr sz
  | Osubcarry sz => Osubcarry_instr sz
  | Oswap     ty => Oswap_instr ty
  end.

(* ------------------------------------------------------------- *)
(* Descriptors for speculative execution operators               *)

(* This define the semantic at the source level.
   Since at source level we do not take into account speculative execution,
   the protect/protect_ptr are simply the identity *)

Definition se_init_sem : wmsf := 0%w.

Definition se_update_sem (b : bool) (msf : wmsf) : wmsf :=
  (if b then msf else (-1%w)%w).

Definition se_move_sem (w : wmsf) : wmsf := w.

Definition se_protect_sem {ws : wsize} (w : word ws) (msf : wmsf) : word ws := w.

Definition se_protect_ptr_sem {len:Z} (t: WArray.array len) (msf : wmsf) : WArray.array len := t.

Definition se_protect_ptr_fail_sem {len:Z} (t: WArray.array len) (msf : wmsf) : exec (WArray.array len) :=
  Let _ := assert (msf == 0%w) ErrSemUndef in
  ok t.

Definition SLHinit_str := "init_msf"%string.
Definition SLHinit_instr :=
  mk_instr_desc_safe (pp_s SLHinit_str)
      [::]
      [::]           (* this info is irrelevant *)
      [:: ty_msf ]
      [:: E 0 ]      (* this info is irrelevant *)
      se_init_sem [:: IBool true ] true DOIT.

Definition SLHupdate_str := "update_msf"%string.
Definition SLHupdate_instr :=
  mk_instr_desc_safe (pp_s SLHupdate_str)
      [:: abool; ty_msf ]
      [:: E 0; E 1 ] (* this info is irrelevant *)
      [:: ty_msf ]
      [:: E 2 ]      (* this info is irrelevant *)
      se_update_sem [:: IBool true ] true DOIT.

Definition SLHmove_str := "mov_msf"%string.
Definition SLHmove_instr :=
  mk_instr_desc_safe (pp_s SLHmove_str)
      [:: ty_msf ]
      [:: E 0 ]      (* this info is irrelevant *)
      [:: ty_msf ]
      [:: E 1 ]      (* this info is irrelevant *)
      se_move_sem [:: IBool true ] true DOIT.

Definition SLHprotect_str := "protect"%string.
Definition SLHprotect_instr ws :=
  mk_instr_desc_safe (pp_sz SLHprotect_str ws)
      [:: aword ws; ty_msf ]
      [:: E 0; E 1 ] (* this info is irrelevant *)
      [:: aword ws ]
      [:: E 2 ]      (* this info is irrelevant *)
      (@se_protect_sem ws) [:: IBool true ] true DOIT.

Lemma protect_ptr_semu n vs vs' v:
  values_uincl vs vs' ->
  @app_sopn_v [::carr n; cty_msf] [::carr n] (sem_prod_ok [:: carr n; cty_msf ] (@se_protect_ptr_sem n)) vs = ok v ->
  exists2 v' : values,
   @app_sopn_v [::carr n; cty_msf] [::carr n] (sem_prod_ok [:: carr n; cty_msf ] (@se_protect_ptr_sem n)) vs' = ok v' &
   values_uincl v v'.
Proof.
  rewrite /app_sopn_v /= => -[] {vs vs'} // v1 v2 + + /of_value_uincl_te -/(_ (carr n)) /= hu.
  move=> [ | v1' [ | ]]; [ by t_xrbindP | | by t_xrbindP].
  move=> _ /List_Forall2_inv_l -[v2' [_ [-> [/of_value_uincl_te -/(_ cty_msf) /= hu' /List_Forall2_inv_l ->]]]].
  t_xrbindP => /= t a /hu [t' -> ha] w' /hu' -> <- <- /=.
  by exists [::Varr t'] => //; constructor.
Qed.

Definition SLHprotect_ptr_str := "protect_ptr"%string.
Definition SLHprotect_ptr_instr ws n :=
  let tin := [:: aarr ws n; ty_msf ] in
  let ctin := map eval_atype tin in
  let semi := @se_protect_ptr_sem (arr_size ws n) in
  {| str      := pp_s SLHprotect_ptr_str;
     tin      := tin;
     i_in     := [:: E 0; E 1 ]; (* this info is irrelevant *)
     tout     := [:: aarr ws n ];
     i_out    := [:: E 2 ]; (* this info is irrelevant *)
     conflicts:=[::];
     i_semi_total := semi;
     i_safe   := [::];
     i_err    := ErrArith;
     i_init   := [:: IBool true ];
     i_valid  := true;
     i_doit   := DOIT;
     i_wf         := refl_equal;
     semu     := semu_eq (tin := ctin) (tout := [:: carr (arr_size ws n)]) (fun _ _ => erefl)
                   (@protect_ptr_semu (arr_size ws n));
  |}.

Lemma protect_ptr_fail_semu n vs vs' v:
  values_uincl vs vs' ->
  @app_sopn_v [::carr n; cty_msf] [::carr n] (@se_protect_ptr_fail_sem n) vs = ok v ->
  exists2 v' : values,
   @app_sopn_v [::carr n; cty_msf] [::carr n] (@se_protect_ptr_fail_sem n) vs' = ok v' &
   values_uincl v v'.
Proof.
  rewrite /app_sopn_v /= => -[] {vs vs'} // v1 v2 + + /of_value_uincl_te -/(_ (carr n)) /= hu.
  move=> [ | v1' [ | ]]; [ by t_xrbindP | | by t_xrbindP].
  move=> _ /List_Forall2_inv_l -[v2' [_ [-> [/of_value_uincl_te -/(_ cty_msf) /= hu' /List_Forall2_inv_l ->]]]].
  rewrite /se_protect_ptr_fail_sem; t_xrbindP => /= t a /hu [t' -> ha] w' /hu' -> /eqP -> <- <- /=.
  by exists [::Varr t'] => //; constructor.
Qed.

Lemma protect_ptr_fail_eq n :
  sem_prod_eq [:: carr n; cty_msf ] (@se_protect_ptr_fail_sem n)
    (@mk_semi [:: carr n; cty_msf ] [:: carr n] [:: sc_is_zero msf_size 1] ErrSemUndef
       [:: IBool true ] (fun (t : WArray.array n) (_ : wmsf) => t)).
Proof.
  move=> t msf.
  rewrite /mk_semi /= /check_safe /= andbT.
  rewrite (safety_cond_holds_is_zero (vs := [:: Varr t; Vword msf]) (k:=1) erefl).
  by rewrite /se_protect_ptr_fail_sem /assert; case: eqP.
Qed.

(* The only safety condition is that the MSF is zero, and the output is
   always defined. *)
Lemma protect_ptr_fail_wf ws n :
  [&& all (safety_cond_wf (map eval_atype [:: aarr ws n; ty_msf])) [:: sc_is_zero msf_size 1],
      all (safety_cond_wf (map eval_atype [:: aarr ws n; ty_msf])) [:: IBool true],
      ssrnat.eqn (size [:: IBool true]) (size [:: aarr ws n])
    & ~~ is_ErrType ErrSemUndef].
Proof. by rewrite /= !andbT safety_cond_wf_is_zero. Qed.

Definition SLHprotect_ptr_fail_str := "protect_ptr_fail"%string.
Definition SLHprotect_ptr_fail_instr ws n :=
  let len := arr_size ws n in
  {| str      := pp_s SLHprotect_ptr_fail_str;
     tin      := [:: aarr ws n; ty_msf ];
     i_in     := [:: E 0; E 1 ]; (* this info is irrelevant *)
     tout     := [:: aarr ws n ];
     i_out    := [:: E 2 ]; (* this info is irrelevant *)
     conflicts:=[::];
     i_semi_total := fun (t : WArray.array len) (_ : wmsf) => t;
     i_safe   := [:: sc_is_zero msf_size 1];
     i_err    := ErrSemUndef;
     i_init   := [:: IBool true ];
     i_valid  := true;
     i_doit   := DOIT;
     i_wf         := protect_ptr_fail_wf ws n;
     semu     := semu_eq (tin := [:: carr len; cty_msf ]) (tout := [:: carr len]) (@protect_ptr_fail_eq len) (@protect_ptr_fail_semu len);
  |}.

Definition slh_op_instruction_desc  (o : slh_op) : instruction_desc :=
  match o with
  | SLHinit               => SLHinit_instr
  | SLHupdate             => SLHupdate_instr
  | SLHmove               => SLHmove_instr
  | SLHprotect ws         => SLHprotect_instr ws
  | SLHprotect_ptr ws n      => SLHprotect_ptr_instr ws n
  | SLHprotect_ptr_fail ws n => SLHprotect_ptr_fail_instr ws n
  end.

(* ---------------------------------------------------------------------- *)

Definition get_instr_desc o :=
  match o with
  | Opseudo_op o => pseudo_op_get_instr_desc o
  | Oslh o => slh_op_instruction_desc o
  | Oasm o       => asm_op_instr o
  end.

Definition string_of_sopn o : string := str (get_instr_desc o) tt.

Definition sopn_tin o : list atype := tin (get_instr_desc o).
Definition sopn_tout o : list atype := tout (get_instr_desc o).

Definition sopn_sem_ o := semi (get_instr_desc o).
Definition sopn_sem o : exec _ :=
  Let _ := assert (get_instr_desc o).(i_valid) ErrType in
  ok (sopn_sem_ o).

Instance eqC_sopn : eqTypeC sopn :=
  { ceqP := sopn_eq_axiom }.

Definition map_prim_constructor {A B} (f: A -> B) (p : prim_constructor A) : prim_constructor B :=
  match p with
  | PrimX86 a k => PrimX86 a (fun x => omap f (k x))
  | PrimARM mk => PrimARM (fun sf ic => Let y := mk sf ic in ok (f y))
  end.

Definition primM {A: Type} f  := @PrimX86 A [::] (fun _ => Some f).
Definition primP {A: Type} (f: wsize -> A) :=
      PrimX86 (map PVp (Uptr :: rem Uptr wsizes))
        (fun s => if s is PVp sz then Some (f sz) else None).

Definition sopn_prim_string : seq (string * prim_constructor sopn) :=
  [::
    ("copy", primP (fun sz => Opseudo_op (Ocopy sz 0)));  (* The size is fixed later *)
    ("swap", primM (Opseudo_op (Oswap abool))); (* The type is fixed later *)
    (* "NOP" is ignored on purpose *)
    ("mulu", primP (fun sz => Opseudo_op (Omulu sz)));
    ("adc", primP (fun sz => Opseudo_op (Oaddcarry sz)));
    ("sbb", primP (fun sz => Opseudo_op (Osubcarry sz)));
    ("init_msf"   , primM (Oslh SLHinit));
    ("update_msf" , primM (Oslh SLHupdate));
    ("mov_msf"    , primM (Oslh SLHmove));
    ("protect"    , primP (fun sz => Oslh (SLHprotect sz)));
    ("protect_ptr", primM (Oslh (SLHprotect_ptr U8 0))) (* The size is fixed later *)
   ]%string
  ++ map (fun '(s, p) => (s, map_prim_constructor Oasm p)) prim_string.

(* used in the OCaml world, it could be a definition it seems *)
Instance asmOp_sopn : asmOp sopn :=
  { asm_op_instr := get_instr_desc;
    prim_string := sopn_prim_string }.

End WITH_PARAMS.
