(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.

Require Import
  pseudo_operator
  sem_type
  shift_kind
  strings
  slh_ops
  type
  values
  var.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Unset Elimination Schemes.

(* ----------------------------------------------------------------------------- *)

Variant arg_desc :=
| ADImplicit  of var
| ADExplicit  of nat & option var.

Record instruction_desc := mkInstruction {
  str      : unit -> string;
  tin      : list stype;
  i_in     : seq arg_desc;
  tout     : list stype;
  i_out    : seq arg_desc;
  semi     : sem_prod tin (exec (sem_tuple tout));
  semu     : forall vs vs' v,
                List.Forall2 value_uincl vs vs' ->
                app_sopn_v semi vs = ok v ->
                exists2 v', app_sopn_v semi vs' = ok v' & List.Forall2 value_uincl v v';
  i_safe   : seq safe_cond;
}.

Arguments semu _ [vs vs' v] _ _.

Notation mk_instr_desc str tin i_in tout i_out semi safe :=
  {| str      := str;
     tin      := tin;
     i_in     := i_in;
     tout     := tout;
     i_out    := i_out;
     semi     := semi;
     semu     := @vuincl_app_sopn_v tin tout semi refl_equal;
     i_safe   := safe;
  |}.

(* -------------------------------------------------------------------- *)

Variant prim_x86_suffix :=
  | PVp of wsize
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
     -> option shift_kind (* has_shift *)
     -> asm_op).

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

Variant internal_reason :=
  (* Register to load the tag to. *)
  | IRpc_load_reg

  (* MSF to protect the tag. *)
  | IRpc_load_msf

  (* Scratch register to spill the tag to an extra register. *)
  | IRpc_save_scratch
.

Scheme Equality for internal_reason.

Lemma internal_reason_eq_axiom : Equality.axiom internal_reason_beq.
Proof.
  exact:
    (eq_axiom_of_scheme
       internal_internal_reason_dec_bl
       internal_internal_reason_dec_lb).
Qed.

Definition internal_reason_eqMixin := Equality.Mixin internal_reason_eq_axiom.
Canonical internal_reason_eqType :=
  Eval hnf in EqType internal_reason internal_reason_eqMixin.

Definition string_of_internal_reason (ir : internal_reason) : string :=
  match ir with
  | IRpc_load_reg => "pc_load_reg"
  | IRpc_load_msf => "pc_load_msf"
  | IRpc_save_scratch => "pc_save_scratch"
  end.

Variant internal_op :=
| Ouse_vars of internal_reason & seq stype & seq stype.

Definition internal_op_beq (io0 io1 : internal_op) : bool :=
  match io0, io1 with
  | Ouse_vars ir0 tin0 tout0, Ouse_vars ir1 tin1 tout1 =>
      [&& ir0 == ir1, tin0 == tin1 & tout0 == tout1 ]
  end.

Lemma internal_op_eq_axiom : Equality.axiom internal_op_beq.
Proof.
  move=> [???] [???].
  rewrite /internal_op_beq.
  apply: (iffP idP).
  - by move=> /and3P [] /eqP -> /eqP -> /eqP ->.
  move=> [-> -> ->].
  by rewrite !eqxx.
Qed.

Definition internal_op_eqMixin := Equality.Mixin internal_op_eq_axiom.
Canonical internal_op_eqType :=
  Eval hnf in EqType internal_op internal_op_eqMixin.

Variant sopn :=
| Opseudo_op of pseudo_operator
| Oslh of slh_op
| Oasm of asm_op_t
| Ointernal of internal_op
.

Definition sopn_beq (o1 o2:sopn) :=
  match o1, o2 with
  | Opseudo_op o1, Opseudo_op o2 => o1 == o2
  | Oslh o1, Oslh o2 => o1 == o2
  | Oasm o1, Oasm o2 => o1 == o2 ::>
  | Ointernal o1, Ointernal o2 => o1 == o2
  | _, _ => false
  end.

Lemma sopn_eq_axiom : Equality.axiom sopn_beq.
Proof.
  move=> [] ? [] ?.
  all: by [ constructor | apply: reflect_inj eqP => ?? [] ].
Qed.

Definition sopn_eqMixin := Equality.Mixin sopn_eq_axiom.
Canonical  sopn_eqType  := EqType sopn sopn_eqMixin.

Definition sopn_copy (ws : wsize) (p : positive) : sopn :=
  Opseudo_op (Ocopy ws p).
Definition sopn_nop : sopn := Opseudo_op Onop.
Definition sopn_mulu (ws : wsize) : sopn := Opseudo_op (Omulu ws).
Definition sopn_addcarry (ws : wsize) : sopn := Opseudo_op (Oaddcarry ws).
Definition sopn_subcarry (ws : wsize) : sopn := Opseudo_op (Osubcarry ws).

(* ------------------------------------------------------------- *)
(* Descriptors for speudo operators                              *)

(* The fields [i_in] and [i_out] are used in the regalloc pass only. The
   following instructions should be replaced before that pass (in lowering),
   thus we do not need to set those fields to true values. We respect the number
   of in- and out- arguments, but apart from that, we give some trivial values.
*)

Local Notation E n := (ADExplicit n None).

Definition Ocopy_instr ws p := 
  let sz := Z.to_pos (arr_size ws p) in
  {| str      := pp_sz "copy" ws;
     tin      := [:: sarr sz];
     i_in     := [:: E 1];
     tout     := [:: sarr sz];
     i_out    := [:: E 0];
     semi     := @WArray.copy ws p;
     semu     := @vuincl_copy ws p;
     i_safe   := [:: AllInit ws p 0];
  |}.

Definition Onop_instr := 
  mk_instr_desc (pp_s "NOP")
           [::] [::]
           [::] [::]
           (ok tt)
           [::].

Definition Omulu_instr sz :=
  mk_instr_desc (pp_sz "mulu" sz)
           [:: sword sz; sword sz]
           [:: E 0; E 1] (* this info is irrelevant *)
           [:: sword sz; sword sz]
           [:: E 2; E 3] (* this info is irrelevant *)
           (fun x y => ok (@wumul sz x y)) [::].
 
Definition Oaddcarry_instr sz :=
  mk_instr_desc (pp_sz "adc" sz)
           [:: sword sz; sword sz; sbool]
           [:: E 0; E 1; E 2] (* this info is irrelevant *)
           [:: sbool; sword sz]
           [:: E 3; E 4]      (* this info is irrelevant *)
           (fun x y c => let p := @waddcarry sz x y c in ok (Some p.1, p.2))
           [::].

Definition Osubcarry_instr sz:= 
  mk_instr_desc (pp_sz "sbb" sz)
           [:: sword sz; sword sz; sbool]
           [:: E 0; E 1; E 2] (* this info is irrelevant *)
           [:: sbool; sword sz]
           [:: E 3; E 4]      (* this info is irrelevant *)
           (fun x y c => let p := @wsubcarry sz x y c in ok (Some p.1, p.2))
           [::].

Definition pseudo_op_get_instr_desc (o : pseudo_operator) : instruction_desc :=
  match o with
  | Ocopy ws p   => Ocopy_instr ws p
  | Onop         => Onop_instr
  | Omulu     sz => Omulu_instr sz
  | Oaddcarry sz => Oaddcarry_instr sz
  | Osubcarry sz => Osubcarry_instr sz
  end.

(* ------------------------------------------------------------- *)
(* Descriptors for speculative execution operators               *)

(* This define the semantic at the source level.
   Since at source level we do not take into account speculative execution,
   the protect/protect_ptr are simply the identity *)

Definition se_init_sem : exec wmsf := ok 0%R.

Definition se_update_sem (b : bool) (msf : wmsf) : exec wmsf :=
  ok (if b then msf else (-1)%R).

Definition se_move_sem (w : wmsf) : exec wmsf := ok w.

Definition se_protect_sem {ws : wsize} (w : word ws) (msf : wmsf) : exec (word ws) := ok w.

Definition se_protect_ptr_sem {p:positive} (t: WArray.array p) (msf : wmsf) : exec (WArray.array p) := ok t.

Definition se_protect_ptr_fail_sem {p:positive} (t: WArray.array p) (msf : wmsf) : exec (WArray.array p) :=
  Let _ := assert (msf == 0%R) ErrType in
  ok t.

Definition SLHinit_str := "init_msf"%string.
Definition SLHinit_instr :=
  mk_instr_desc (pp_s SLHinit_str)
      [::]
      [::]           (* this info is irrelevant *)
      [:: ty_msf ]
      [:: E 0 ]      (* this info is irrelevant *)
      se_init_sem
      [::].

Definition SLHupdate_str := "update_msf"%string.
Definition SLHupdate_instr :=
  mk_instr_desc (pp_s SLHupdate_str)
      [:: sbool; ty_msf ]
      [:: E 0; E 1 ] (* this info is irrelevant *)
      [:: ty_msf ]
      [:: E 2 ]      (* this info is irrelevant *)
      se_update_sem
      [::].

Definition SLHmove_str := "mov_msf"%string.
Definition SLHmove_instr :=
  mk_instr_desc (pp_s SLHmove_str)
      [:: ty_msf ]
      [:: E 0 ]      (* this info is irrelevant *)
      [:: ty_msf ]
      [:: E 1 ]      (* this info is irrelevant *)
      se_move_sem
      [::].

Definition SLHprotect_str := "protect"%string.
Definition SLHprotect_instr ws :=
  mk_instr_desc (pp_sz SLHprotect_str ws)
      [:: sword ws; ty_msf ]
      [:: E 0; E 1 ] (* this info is irrelevant *)
      [:: sword ws ]
      [:: E 2 ]      (* this info is irrelevant *)
      (@se_protect_sem ws)
      [::].

Lemma protect_ptr_semu p vs vs' v:
  List.Forall2 value_uincl vs vs' ->
  @app_sopn_v [::sarr p; ty_msf] [::sarr p] (@se_protect_ptr_sem p) vs = ok v ->
  exists2 v' : values,
   @app_sopn_v [::sarr p; ty_msf] [::sarr p] (@se_protect_ptr_sem p) vs' = ok v' &
   List.Forall2 value_uincl v v'.
Proof.
  rewrite /app_sopn_v /= => -[] {vs vs'} // v1 v2 + + /of_value_uincl_te -/(_ (sarr p)) /= hu.
  move=> [ | v1' [ | ]]; [ by t_xrbindP | | by t_xrbindP].
  move=> _ /List_Forall2_inv_l -[v2' [_ [-> [/of_value_uincl_te -/(_ ty_msf) /= hu' /List_Forall2_inv_l ->]]]].
  t_xrbindP => /= t a /hu [t' -> ha] w' /hu' -> [<-] <- /=.
  by exists [::Varr t'] => //; constructor.
Qed.

Definition SLHprotect_ptr_str := "protect_ptr"%string.
Definition SLHprotect_ptr_instr p :=
  {| str      := pp_s SLHprotect_ptr_str;
     tin      := [:: sarr p; ty_msf ];
     i_in     := [:: E 0; E 1 ]; (* this info is irrelevant *)
     tout     := [:: sarr p ];
     i_out    := [:: E 2 ]; (* this info is irrelevant *)
     semi     := @se_protect_ptr_sem p;
     semu     := @protect_ptr_semu p;
     i_safe   := [::];
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

Definition SLHprotect_ptr_fail_str := "protect_ptr_fail"%string.
Definition SLHprotect_ptr_fail_instr p :=
  {| str      := pp_s SLHprotect_ptr_fail_str;
     tin      := [:: sarr p; ty_msf ];
     i_in     := [:: E 0; E 1 ]; (* this info is irrelevant *)
     tout     := [:: sarr p ];
     i_out    := [:: E 2 ]; (* this info is irrelevant *)
     semi     := @se_protect_ptr_fail_sem p;
     semu     := @protect_ptr_fail_semu p;
     i_safe   := [::];
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

Fixpoint mk_ltuple
  (get : forall ty, sem_ot ty) (tout : seq stype) : sem_tuple tout :=
  match tout with
  | [::] => tt
  | [:: t0 ] => get t0
  | t0 :: t1 :: tout1 =>
    let rest := mk_ltuple get tout1 in
    let rest := @merge_tuple [:: sem_ot t1 ] (map sem_ot tout1) (get t1) rest in
    (:: get t0 & rest)
  end.

Definition default_value (t : stype) : sem_ot t :=
  match t with
  | sbool => None
  | sint => 0%Z
  | sword ws => 0%R
  | sarr n => WArray.empty n
  end.

Fixpoint use_vars_semi
  (tin tout : seq stype) : sem_prod tin (exec (sem_tuple tout)) :=
  match tin with
  | [::] => ok (mk_ltuple default_value tout)
  | _ :: tin => fun _ => use_vars_semi tin tout
  end.

Lemma use_vars_semu tin tout vargs vargs' vres :
  List.Forall2 value_uincl vargs vargs' ->
  app_sopn_v (use_vars_semi tin tout) vargs = ok vres ->
  exists2 vres',
    app_sopn_v (use_vars_semi tin tout) vargs' = ok vres'
    & List.Forall2 value_uincl vres vres'.
Proof.
  elim: tin vargs vargs' => [|tin0 tin hind] vargs vargs'.
  - case: vargs => //.
    move=> /List_Forall2_inv_l ?; subst vargs'.
    case: tout => [|tout0 tout].
    + move=> [?]; subst vres. rewrite /app_sopn_v /=. by eexists.
    move=> ->. eexists; first done. exact: List_Forall2_refl.

  case: vargs => // v vargs.
  move=> /List_Forall2_inv_l [v' [vargs'' [? [hvv' hvargs]]]];
    subst vargs'.
  rewrite /app_sopn_v /=.
  t_xrbindP=> vres0 v0 hv0 h ?; subst vres.
  have [? -> ?] /= := val_uincl_of_val hvv' hv0.
  move: (hind _ _ hvargs) => [].
  - by rewrite /app_sopn_v h /=.
  move=> vres.
  rewrite /app_sopn_v.
  t_xrbindP=> vres1 -> ? ?; subst vres.
  by eexists.
Qed.

Arguments use_vars_semu _ _ : clear implicits.

(* The concrete indexes we use for [i_in] are irrelevant, as long as there is
   one per type and they don't overlap with [i_out]. *)
Definition use_vars_instr
  (ir : internal_reason) (tin tout : seq stype) : instruction_desc :=
  {|
    str := pp_s (append "use_vars." (string_of_internal_reason ir));
    tin := tin;
    i_in := map (fun n => ADExplicit n None) (iota 0 (size tin));
    tout := tout;
    i_out := map (fun n => ADExplicit n None) (iota (size tin) (size tout));
    semi := use_vars_semi tin tout;
    semu := use_vars_semu tin tout;
    i_safe := [::];
  |}.

Definition internal_op_instr_desc (o : internal_op) : instruction_desc :=
  match o with
  | Ouse_vars ir tin tout => use_vars_instr ir tin tout
  end.

(* ---------------------------------------------------------------------- *)

Definition get_instr_desc o :=
  match o with
  | Opseudo_op o => pseudo_op_get_instr_desc o
  | Oslh o => slh_op_instruction_desc o
  | Oasm o       => asm_op_instr o
  | Ointernal o => internal_op_instr_desc o
  end.

Definition string_of_sopn o : string := str (get_instr_desc o) tt.

Definition sopn_tin o : list stype := tin (get_instr_desc o).
Definition sopn_tout o : list stype := tout (get_instr_desc o).
Definition sopn_sem  o := semi (get_instr_desc o).

Instance eqC_sopn : eqTypeC sopn :=
  { ceqP := sopn_eq_axiom }.

Definition map_prim_constructor {A B} (f: A -> B) (p : prim_constructor A) : prim_constructor B :=
  match p with
  | PrimX86 a k => PrimX86 a (fun x => Option.bind (olift f) (k x))
  | PrimARM x => PrimARM (fun sf ic hs => f (x sf ic hs))
  end.

Definition primM {A: Type} f  := @PrimX86 A [::] (fun _ => Some f).
Definition primP {A: Type} (f: wsize -> A) :=
      PrimX86 (map PVp (Uptr :: rem Uptr wsizes))
        (fun s => if s is PVp sz then Some (f sz) else None).

Definition sopn_prim_string : seq (string * prim_constructor sopn) :=
  [::
    ("copy", primP (fun sz => Opseudo_op (Ocopy sz xH)));  (* The size is fixed later *)
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
