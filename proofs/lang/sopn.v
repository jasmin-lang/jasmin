(* ** Imports and settings *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype ssralg.

Require Import
  pseudo_operator
  sem_type
  shift_kind
  strings
  slh_ops
  type
  values
  var.

Local Unset Elimination Schemes.

(* ----------------------------------------------------------------------------- *)
Variant arg_constrained_register :=
| ACR_any
| ACR_exact of var
| ACR_vector of var
| ACR_subset of seq var
.

Variant arg_desc :=
| ADImplicit  of var
| ADExplicit  of nat & arg_constrained_register.

Variant arg_position :=
| APout of nat
| APin of nat.

Record instruction_desc := mkInstruction {
  str      : unit -> string;
  tin      : list stype;
  i_in     : seq arg_desc;
  tout     : list stype;
  i_out    : seq arg_desc;
  conflicts: seq (arg_position * arg_position);
  semi     : sem_prod tin (exec (sem_tuple tout));
  semu     : forall vs vs' v,
                List.Forall2 value_uincl vs vs' ->
                app_sopn_v semi vs = ok v ->
                exists2 v', app_sopn_v semi vs' = ok v' & List.Forall2 value_uincl v v';
  (* This field allows to ensure the validity of the instruction,
     it is usefull when the its name allows to encode more instructions than the real existing one.
     See field id_valid in arch/arch_decl.v
  *)
  i_valid  : bool;
  i_safe   : seq safe_cond;
  (* Extra properties ensuring that previous information are consistent *)
  i_safe_wf    : all (fun sc => ssrnat.leq (sc_needed_args sc) (size tin)) i_safe;
    (* id_semi does not generates type error *)
  i_semi_errty : i_valid -> sem_forall (fun r => r <> Error ErrType) tin semi;
    (* safety condition are sufficient to ensure that no error are raised *)
  i_semi_safe  : i_valid -> interp_safe_cond_ty i_safe semi;
}.

Arguments semu _ [vs vs' v] _ _.

Notation mk_instr_desc str tin i_in tout i_out semi safe valid semi_errty semi_safe :=
  {| str          := str;
     tin          := tin;
     i_in         := i_in;
     tout         := tout;
     i_out        := i_out;
     conflicts    := [::];
     semi         := semi;
     semu         := @vuincl_app_sopn_v tin tout semi refl_equal;
     i_safe       := safe;
     i_valid      := valid;
     i_safe_wf    := refl_equal;
     i_semi_errty := semi_errty;
     i_semi_safe  := semi_safe;
  |}.

Notation mk_instr_desc_safe str tin i_in tout i_out semi valid :=
  (mk_instr_desc str tin i_in tout i_out (sem_prod_ok tin semi) [::] valid
     (fun _ => (@sem_prod_ok_error _ tin semi ErrType))
     (fun _ => (@sem_prod_ok_safe _ tin semi)))
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

Definition sopn_copy (ws : wsize) (p : positive) : sopn :=
  Opseudo_op (Ocopy ws p).
Definition sopn_nop : sopn := Opseudo_op Onop.
Definition sopn_mulu (ws : wsize) : sopn := Opseudo_op (Omulu ws).
Definition sopn_addcarry (ws : wsize) : sopn := Opseudo_op (Oaddcarry ws).
Definition sopn_subcarry (ws : wsize) : sopn := Opseudo_op (Osubcarry ws).

Definition is_Oslh (op : sopn) : option slh_op :=
  if op is Oslh op then Some op else None.

Lemma is_OslhP op : is_reflect Oslh op (is_Oslh op).
Proof. case: op; by constructor. Qed.


(* ------------------------------------------------------------- *)
(* Descriptors for speudo operators                              *)

(* The fields [i_in] and [i_out] are used in the regalloc pass only. The
   following instructions should be replaced before that pass (in lowering),
   thus we do not need to set those fields to true values. We respect the number
   of in- and out- arguments, but apart from that, we give some trivial values.
*)

Local Notation E n := (ADExplicit n ACR_any).

Lemma array_copy_errty ws p:
  let sz := Z.to_pos (arr_size ws p) in
  let tin := [:: sarr sz] in
  let semi := @WArray.copy ws p in
  sem_forall (fun r : result error (sem_tuple [:: sarr sz]) => r <> Error ErrType) tin semi.
Proof.
  move=> /= t; rewrite /WArray.copy /WArray.fcopy.
  elim: ziota (WArray.empty _) => // j js hrec t1 /=.
  rewrite {2}/WArray.get /read.
  case: is_aligned_if => //.
  case heq: mapM => [w_s | e] /=; last first.
  + elim: ziota heq => //= ?? hrec'.
    rewrite {2}/WArray.get8.
    case: WArray.in_bound; last by move=> [<-].
    by case: WArray.is_init => //=; [ case: mapM hrec' | move=> [<-]].
  case heq': WArray.set => [t' | e] /=; first by apply hrec.
  move: heq'; rewrite /WArray.set /write.
  case: is_aligned_if => //; last by move=> [<-].
  elim: ziota t1 => // ?? hrec' /= t1.
  rewrite {2}/WArray.set8; case: WArray.in_bound => [ | [<-]] //=; apply: hrec'.
Qed.

Lemma array_copy_safe ws p:
  let sz := Z.to_pos (arr_size ws p) in
  let tin := [:: sarr sz] in
  let semi := @WArray.copy ws p in
  interp_safe_cond_ty (tin:=tin) [:: AllInit ws p 0] semi.
Proof.
  move=> /= t /= h; have /= {h} := List.Forall_inv h.
  rewrite WArray.castK => /(_ _ erefl) h.
  rewrite /WArray.copy /WArray.fcopy; move: (WArray.empty _).
  apply ziota_ind.
  + by move=> /=; eauto.
  move=> j js hj hrec t1 /=.
  have [w -> /=] := h _ hj; rewrite /WArray.set.
  have := [elaborate (writeV (CM:= WArray.array_CM (Z.to_pos (arr_size ws p))))].
  move => /(_ _ w t1 Aligned (j * mk_scale AAscale ws)%Z) wP.
  assert (h1 : validw t1 Aligned (j * mk_scale AAscale ws)%Z ws).
  + rewrite /validw /is_aligned_if WArray.is_align_scale andTb.
    apply ziota_ind => //= i ? hi ->; rewrite andbT; apply/WArray.in_boundP.
    rewrite WArray.addE; change (Zpos _) with ((wsize_size ws) * p)%Z;Lia.nia.
  move/wP: h1 => [t2 ->] /=; apply hrec.
Qed.

Definition Ocopy_instr ws p :=
  let sz := Z.to_pos (arr_size ws p) in
  {| str      := pp_sz "copy" ws;
     tin      := [:: sarr sz];
     i_in     := [:: E 1];
     tout     := [:: sarr sz];
     i_out    := [:: E 0];
     conflicts:= [::];
     semi     := @WArray.copy ws p;
     semu     := @vuincl_copy ws p;
     i_valid  := true;
     i_safe   := [:: AllInit ws p 0];
     i_safe_wf    := refl_equal;
     i_semi_errty := fun _ => (@array_copy_errty ws p);
     i_semi_safe  := fun _ => (@array_copy_safe ws p);
  |}.

Definition Onop_instr :=
  mk_instr_desc_safe (pp_s "NOP")
           [::] [::]
           [::] [::]
           tt
           true.

Definition Omulu_instr sz :=
  mk_instr_desc_safe (pp_sz "mulu" sz)
           [:: sword sz; sword sz]
           [:: E 0; E 1] (* this info is irrelevant *)
           [:: sword sz; sword sz]
           [:: E 2; E 3] (* this info is irrelevant *)
           (@wumul sz) true.

Definition Oaddcarry_instr sz :=
  mk_instr_desc_safe (pp_sz "adc" sz)
           [:: sword sz; sword sz; sbool]
           [:: E 0; E 1; E 2] (* this info is irrelevant *)
           [:: sbool; sword sz]
           [:: E 3; E 4]      (* this info is irrelevant *)
           (fun x y c => let p := @waddcarry sz x y c in (Some p.1, p.2))
           true.

Definition Osubcarry_instr sz :=
  mk_instr_desc_safe (pp_sz "sbb" sz)
           [:: sword sz; sword sz; sbool]
           [:: E 0; E 1; E 2] (* this info is irrelevant *)
           [:: sbool; sword sz]
           [:: E 3; E 4]      (* this info is irrelevant *)
           (fun x y c => let p := @wsubcarry sz x y c in (Some p.1, p.2))
           true.

Fixpoint spill_semi (tys: seq stype) : sem_prod tys (sem_tuple [::]):=
  match tys as tys0 return sem_prod tys0 (sem_tuple [::]) with
  | [::] => tt
  | t::tys => fun (_ : sem_t t) => spill_semi tys
  end.

Lemma spill_semu tys (vs vs' : seq value) (v : values) :
   List.Forall2 value_uincl vs vs' ->
   app_sopn_v (sem_prod_ok tys (spill_semi tys)) vs = ok v ->
   exists2 v' : values, app_sopn_v (sem_prod_ok tys (spill_semi tys)) vs' = ok v' &
                        List.Forall2 value_uincl v v'.
Proof.
  rewrite /app_sopn_v; elim: tys vs vs' v => /= [ | t tys hrec] ?? v; case => //=.
  + by move=> [<-]; exists [::].
  move=> v1 v1' vs vs' huv hu /=; t_xrbindP => ?? hv ha <-.
  have [? -> _ /=]:= val_uincl_of_val huv hv.
  by apply: hrec;[ apply hu | rewrite ha].
Qed.

Definition Ospill_instr o tys :=
  let semi := spill_semi tys in
  {| str      := (fun _ => string_of_pseudo_operator (Ospill o tys));
     tin      := tys;
     i_in     := mapi (fun i _ => E i) tys;
     tout     := [:: ];
     i_out    := [:: ];
     conflicts:= [::];
     semi     := sem_prod_ok tys semi;
     semu     := @spill_semu tys;
     i_safe   := [:: ];
     i_valid  := true;
     i_safe_wf    := refl_equal;
     i_semi_errty := fun _ => (@sem_prod_ok_error _ tys semi ErrType);
     i_semi_safe  := fun _ => (@sem_prod_ok_safe _ tys semi);
  |}.

Definition Oswap_instr ty :=
  let tin := [:: ty; ty] in
  let semi := @swap_semi ty in
  {| str    := (fun _ => "swap"%string);
     tin    := tin;
     i_in   := [:: E 0; E 1]; (* this info is relevant *)
     tout   := [:: ty; ty];
     i_out  := [:: E 0; E 1]; (* this info is relevant *)
     conflicts:= [::];
     semi   := sem_prod_ok tin semi;
     semu   := @swap_semu ty;
     i_safe := [::];
     i_valid := true;
     i_safe_wf    := refl_equal;
     i_semi_errty := fun _ => (@sem_prod_ok_error _ tin semi ErrType);
     i_semi_safe  := fun _ => (@sem_prod_ok_safe _ tin semi);
  |}.

Definition pseudo_op_get_instr_desc (o : pseudo_operator) : instruction_desc :=
  match o with
  | Ospill o tys => Ospill_instr o tys
  | Ocopy ws p   => Ocopy_instr ws p
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

Definition se_init_sem : wmsf := 0%R.

Definition se_update_sem (b : bool) (msf : wmsf) : wmsf :=
  (if b then msf else (-1)%R).

Definition se_move_sem (w : wmsf) : wmsf := w.

Definition se_protect_sem {ws : wsize} (w : word ws) (msf : wmsf) : word ws := w.

Definition se_protect_ptr_sem {p:positive} (t: WArray.array p) (msf : wmsf) : WArray.array p := t.

Definition se_protect_ptr_fail_sem {p:positive} (t: WArray.array p) (msf : wmsf) : exec (WArray.array p) :=
  Let _ := assert (msf == 0%R) ErrSemUndef in
  ok t.

Definition SLHinit_str := "init_msf"%string.
Definition SLHinit_instr :=
  mk_instr_desc_safe (pp_s SLHinit_str)
      [::]
      [::]           (* this info is irrelevant *)
      [:: ty_msf ]
      [:: E 0 ]      (* this info is irrelevant *)
      se_init_sem
      true.

Definition SLHupdate_str := "update_msf"%string.
Definition SLHupdate_instr :=
  mk_instr_desc_safe (pp_s SLHupdate_str)
      [:: sbool; ty_msf ]
      [:: E 0; E 1 ] (* this info is irrelevant *)
      [:: ty_msf ]
      [:: E 2 ]      (* this info is irrelevant *)
      se_update_sem
      true.

Definition SLHmove_str := "mov_msf"%string.
Definition SLHmove_instr :=
  mk_instr_desc_safe (pp_s SLHmove_str)
      [:: ty_msf ]
      [:: E 0 ]      (* this info is irrelevant *)
      [:: ty_msf ]
      [:: E 1 ]      (* this info is irrelevant *)
      se_move_sem
      true.

Definition SLHprotect_str := "protect"%string.
Definition SLHprotect_instr ws :=
  mk_instr_desc_safe (pp_sz SLHprotect_str ws)
      [:: sword ws; ty_msf ]
      [:: E 0; E 1 ] (* this info is irrelevant *)
      [:: sword ws ]
      [:: E 2 ]      (* this info is irrelevant *)
      (@se_protect_sem ws)
      true.

Lemma protect_ptr_semu p vs vs' v:
  List.Forall2 value_uincl vs vs' ->
  @app_sopn_v [::sarr p; ty_msf] [::sarr p] (sem_prod_ok [:: sarr p; ty_msf ] (@se_protect_ptr_sem p)) vs = ok v ->
  exists2 v' : values,
   @app_sopn_v [::sarr p; ty_msf] [::sarr p] (sem_prod_ok [:: sarr p; ty_msf ] (@se_protect_ptr_sem p)) vs' = ok v' &
   List.Forall2 value_uincl v v'.
Proof.
  rewrite /app_sopn_v /= => -[] {vs vs'} // v1 v2 + + /of_value_uincl_te -/(_ (sarr p)) /= hu.
  move=> [ | v1' [ | ]]; [ by t_xrbindP | | by t_xrbindP].
  move=> _ /List_Forall2_inv_l -[v2' [_ [-> [/of_value_uincl_te -/(_ ty_msf) /= hu' /List_Forall2_inv_l ->]]]].
  t_xrbindP => /= t a /hu [t' -> ha] w' /hu' -> <- <- /=.
  by exists [::Varr t'] => //; constructor.
Qed.

Definition SLHprotect_ptr_str := "protect_ptr"%string.
Definition SLHprotect_ptr_instr p :=
  let tin := [:: sarr p; ty_msf ] in
  let semi := @se_protect_ptr_sem p in
  {| str      := pp_s SLHprotect_ptr_str;
     tin      := tin;
     i_in     := [:: E 0; E 1 ]; (* this info is irrelevant *)
     tout     := [:: sarr p ];
     i_out    := [:: E 2 ]; (* this info is irrelevant *)
     conflicts:=[::];
     semi     := sem_prod_ok tin semi;
     semu     := @protect_ptr_semu p;
     i_safe   := [::];
     i_valid  := true;
     i_safe_wf    := refl_equal;
     i_semi_errty := fun _ => (@sem_prod_ok_error _ tin semi ErrType);
     i_semi_safe  := fun _ => (@sem_prod_ok_safe _ tin semi);
  |}.

Lemma protect_ptr_fail_semu p vs vs' v:
  List.Forall2 value_uincl vs vs' ->
  @app_sopn_v [::sarr p; ty_msf] [::sarr p] (@se_protect_ptr_fail_sem p) vs = ok v ->
  exists2 v' : values,
   @app_sopn_v [::sarr p; ty_msf] [::sarr p] (@se_protect_ptr_fail_sem p) vs' = ok v' &
   List.Forall2 value_uincl v v'.
Proof.
  rewrite /app_sopn_v /= => -[] {vs vs'} // v1 v2 + + /of_value_uincl_te -/(_ (sarr p)) /= hu.
  move=> [ | v1' [ | ]]; [ by t_xrbindP | | by t_xrbindP].
  move=> _ /List_Forall2_inv_l -[v2' [_ [-> [/of_value_uincl_te -/(_ ty_msf) /= hu' /List_Forall2_inv_l ->]]]].
  rewrite /se_protect_ptr_fail_sem; t_xrbindP => /= t a /hu [t' -> ha] w' /hu' -> /eqP -> <- <- /=.
  by rewrite eqxx /=; exists [::Varr t'] => //; constructor.
Qed.

Lemma protect_ptr_fail_errty p:
  let tin := [:: sarr p; ty_msf ] in
  let semi := @se_protect_ptr_fail_sem p in
  sem_forall (fun r : result error (sem_tuple [:: sarr p]) => r <> Error ErrType) tin semi.
Proof. by rewrite /= /se_protect_ptr_fail_sem => t msf; case: eqP. Qed.

(* Remark the safety condition is stronger than needed but it
   is not important because the instruction is not visible at Jasmin source level.
   This instruction is only used internally.
*)
Lemma protect_ptr_fail_safe p:
  let tin := [:: sarr p; ty_msf ] in
  let semi := @se_protect_ptr_fail_sem p in
  interp_safe_cond_ty (tin:=tin) [:: ScFalse] semi.
Proof.
  by rewrite /interp_safe_cond_ty /= => t msf h; have := List.Forall_inv h.
Qed.

Definition SLHprotect_ptr_fail_str := "protect_ptr_fail"%string.
Definition SLHprotect_ptr_fail_instr p :=
  {| str      := pp_s SLHprotect_ptr_fail_str;
     tin      := [:: sarr p; ty_msf ];
     i_in     := [:: E 0; E 1 ]; (* this info is irrelevant *)
     tout     := [:: sarr p ];
     i_out    := [:: E 2 ]; (* this info is irrelevant *)
     conflicts:=[::];
     semi     := @se_protect_ptr_fail_sem p;
     semu     := @protect_ptr_fail_semu p;
     i_safe   := [:: ScFalse]; (* See remark on protect_ptr_fail_safe *)
     i_valid  := true;
     i_safe_wf    := refl_equal;
     i_semi_errty := fun _ => (@protect_ptr_fail_errty p);
     i_semi_safe  := fun _ => (@protect_ptr_fail_safe p);
  |}.

Definition slh_op_instruction_desc  (o : slh_op) : instruction_desc :=
  match o with
  | SLHinit               => SLHinit_instr
  | SLHupdate             => SLHupdate_instr
  | SLHmove               => SLHmove_instr
  | SLHprotect ws         => SLHprotect_instr ws
  | SLHprotect_ptr p      => SLHprotect_ptr_instr p
  | SLHprotect_ptr_fail p => SLHprotect_ptr_fail_instr p
  end.

(* ---------------------------------------------------------------------- *)

Definition get_instr_desc o :=
  match o with
  | Opseudo_op o => pseudo_op_get_instr_desc o
  | Oslh o => slh_op_instruction_desc o
  | Oasm o       => asm_op_instr o
  end.

Definition string_of_sopn o : string := str (get_instr_desc o) tt.

Definition sopn_tin o : list stype := tin (get_instr_desc o).
Definition sopn_tout o : list stype := tout (get_instr_desc o).

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
    ("copy", primP (fun sz => Opseudo_op (Ocopy sz xH)));  (* The size is fixed later *)
    ("swap", primM (Opseudo_op (Oswap sbool))); (* The type is fixed later *)
    (* "NOP" is ignored on purpose *)
    ("mulu", primP (fun sz => Opseudo_op (Omulu sz)));
    ("adc", primP (fun sz => Opseudo_op (Oaddcarry sz)));
    ("sbb", primP (fun sz => Opseudo_op (Osubcarry sz)));
    ("init_msf"   , primM (Oslh SLHinit));
    ("update_msf" , primM (Oslh SLHupdate));
    ("mov_msf"    , primM (Oslh SLHmove));
    ("protect"    , primP (fun sz => Oslh (SLHprotect sz)));
    ("protect_ptr", primM (Oslh (SLHprotect_ptr xH))) (* The size is fixed later *)
   ]%string
  ++ map (fun '(s, p) => (s, map_prim_constructor Oasm p)) prim_string.

(* used in the OCaml world, it could be a definition it seems *)
Instance asmOp_sopn : asmOp sopn :=
  { asm_op_instr := get_instr_desc;
    prim_string := sopn_prim_string }.

End WITH_PARAMS.

