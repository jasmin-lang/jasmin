(* -------------------------------------------------------------------- *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import xseq strings utils var type values sopn expr fexpr arch_decl.
Require Import compiler_util.

Section ToIdent.

Context (t:ltype) (T:Type) {tS: ToString t T}.

Class ToIdent :=
  { to_ident     : T -> Ident.ident (* Try to not use it *)
  ; of_ident     : Ident.ident -> option T
  ; inj_to_ident : injective to_ident
  ; of_identE    : forall x, of_ident x = assoc [seq (to_ident r, r) | r <- cenum ] x
  }.

Let T_eqType := ceqT_eqType. Canonical T_eqType.

Context {toI : ToIdent}.

Lemma to_ident_uniq : uniq [seq to_ident r | r <- cenum].
Proof.
  rewrite map_inj_in_uniq.
  + by apply count_mem_uniq => x; rewrite mem_cenum /= cenumP.
  by move=> r1 r2 _ _; apply: inj_to_ident.
Qed.

Lemma to_identK : pcancel to_ident of_ident.
Proof.
  move=> r; rewrite of_identE; apply/assocP; first by rewrite -map_comp to_ident_uniq.
  by apply: map_f; rewrite mem_cenum.
Qed.

Lemma of_identI x r : of_ident x = Some r -> to_ident r = x.
Proof.
  by rewrite of_identE => /assocP; rewrite -map_comp => -/(_ to_ident_uniq) /mapP [r' _ []] -> ->.
Qed.

(* -------------------------------------------------------------------- *)

(* Try to not use it *)
Definition to_var r :=
  {| vtype := atype_of_ltype rtype; vname := to_ident r |}.

Definition of_var (v:var) :=
  if v.(vtype) == atype_of_ltype rtype then of_ident v.(vname)
  else None.

Lemma to_varK : pcancel to_var of_var.
Proof. by move=> ?; rewrite /to_var /of_var /= eq_refl to_identK. Qed.

Lemma inj_to_var : injective to_var.
Proof. apply: pcan_inj to_varK. Qed.
Global Arguments inj_to_var {_ _}.

Lemma of_varI {v r} : of_var v = Some r -> to_var r = v.
Proof.
  rewrite /of_var /= /to_var; case: eqP => // heq /of_identI.
  by case: v heq => /= ?? -> <-.
Qed.

End ToIdent.
Arguments ToIdent [t] T%_type_scope {tS}.
Arguments of_var {t} {T}%_type_scope {tS toI} v.
Arguments to_var {t} {T}%_type_scope {tS toI} r.

Module Type MkToIdent_T.

  Parameter mk : forall (t:ltype) (T:Type) {tS: ToString t T},
    (string -> Ident.ident) -> result pp_error_loc (ToIdent T).

End MkToIdent_T.

Module MkToIdent : MkToIdent_T.

  Section Section.
  Import Ident.

  Context (t:ltype) (T:Type) {tS: ToString t T}
        (mk_id : string -> ident).

  Let rid := map (fun r => (r, mk_id (to_string r))) cenum.

  Lemma rid_cenum : unzip1 rid = cenum.
  Proof. by rewrite /rid /unzip1 -map_comp map_id. Qed.

  Let T_eqType := ceqT_eqType. Canonical T_eqType.

  Lemma assoc_rid (r : T) : assoc rid r = Some (mk_id (to_string r)).
  Proof.
    apply/assocP.
    + rewrite -/(unzip1 rid) rid_cenum.
      by apply count_mem_uniq => x; rewrite mem_cenum /= cenumP.
    by apply: map_f; rewrite mem_cenum.
  Qed.

  Lemma assoc_None (r : T) : assoc rid r <> None.
  Proof. by rewrite assoc_rid. Qed.

  Let to_ident (r:T) : ident :=
    match assoc rid r as a return a <> None -> ident with
    | Some id => fun _ => id
    | None => fun h => match h erefl with end
    end (@assoc_None r).

  Lemma to_identE r : to_ident r = mk_id (to_string r).
  Proof. by rewrite /to_ident; move: (assoc_None (r:=r)); rewrite assoc_rid. Qed.

  Let ids := unzip2 rid.

  Lemma to_identI : uniq ids -> injective to_ident.
  Proof.
    move=> hu x y; rewrite !to_identE => heq.
    move: (assoc_rid y); rewrite -heq.
    by apply: assoc_inj (assoc_rid x).
  Qed.

  Let rtbl := foldr (fun '(r,id) t => Mid.set t id r) (Mid.empty _) rid.

  Let of_ident x := Mid.get rtbl x.

  Lemma of_IdentE x :
    of_ident x = assoc [seq (to_ident r, r) | r <- cenum] x.
  Proof.
    have -> : assoc [seq (to_ident r, r) | r <- cenum] x =
              assoc (map (fun p => (p.2, p.1)) rid) x.
    + rewrite /rid -map_comp /comp /=; f_equal.
      by apply: eq_map => r; rewrite to_identE.
    rewrite /of_ident /ids /unzip2 /rtbl /rid -!map_comp /comp /= .
    elim: cenum => /= [ | r rs hrec] /=; first by rewrite Mid.get0.
    by rewrite Mid.setP eq_sym; case: eqP.
  Qed.

  Definition mk :=
    match @idP (uniq ids) with
    | ReflectT is_uniq =>
        ok {| inj_to_ident := to_identI is_uniq
            ; of_identE := of_IdentE
            |}
    | _ => Error (pp_internal_error_s "to_ident generation" category)
    end.

  End Section.

End MkToIdent.

Section ARCH.

Context `{arch : arch_decl}.

Class arch_toIdent :=
  { toI_r  : ToIdent reg
  ; toI_rx : ToIdent regx
  ; toI_x  : ToIdent xreg
  ; toI_f  : ToIdent rflag
  ; inj_toI_reg_regx : forall (r:reg) (rx:regx), to_ident r <> to_ident rx
  }.

#[global]
Existing Instances toI_r toI_rx toI_x toI_f.

End ARCH.

Module Type AToIdent_T.

  Parameter mk :
    forall `{arch : arch_decl},
      (reg_kind -> ltype -> string -> Ident.ident) ->  result pp_error_loc arch_toIdent.

End AToIdent_T.

Module MkAToIdent : AToIdent_T.

  Section Section.
  Context `{arch : arch_decl}.

  Section AUX.

  Context {rtI : ToIdent reg} {rxtI : ToIdent regx}.

  Definition _inj_toI_reg_regx :=
     all (fun r:reg => all (fun rx:regx => to_ident r != to_ident rx) cenum) cenum.

  Let r_eqType  := ceqT_eqType (T:= reg).  Canonical r_eqType.
  Let rx_eqType := ceqT_eqType (T:= regx). Canonical rx_eqType.

  Lemma inj_toI_reg_regxP : _inj_toI_reg_regx ->
    forall (r:reg) (rx:regx), to_ident r <> to_ident rx.
  Proof.
    rewrite /_inj_toI_reg_regx => /allP h r rx.
    have := h r; rewrite mem_cenum /= => /(_ erefl) /allP hx.
    by have := hx rx; rewrite mem_cenum /= => /(_ erefl) /eqP.
  Qed.

  End AUX.

  Definition mk (toid : reg_kind -> ltype -> string -> Ident.ident) :=
    Let toI_r  := MkToIdent.mk (T:= reg) (toid Normal (lword reg_size)) in
    Let toI_rx := MkToIdent.mk (T:= regx) (toid Extra (lword reg_size)) in
    Let toI_x  := MkToIdent.mk (T:= xreg) (toid Normal (lword xreg_size)) in
    Let toI_f  := MkToIdent.mk (T:= rflag) (toid Normal lbool) in
    match @idP _inj_toI_reg_regx with
    | ReflectT h =>
        ok {| toI_r := toI_r
            ; toI_rx := toI_rx
            ; toI_x  := toI_x
            ; toI_f  := toI_f
            ; inj_toI_reg_regx := inj_toI_reg_regxP h
           |}
    | _ => Error (pp_internal_error_s "arch_to_ident generation" "inj_toI_reg_regx")
    end.

  End Section.

End MkAToIdent.

Section ARCH.

Context `{arch : arch_decl} {atoI : arch_toIdent}.

Lemma to_var_reg_neq_regx (r : reg_t) (x : regx_t) :
  to_var r <> to_var x.
Proof. rewrite /to_var => -[]; apply: inj_toI_reg_regx. Qed.

Lemma to_var_reg_neq_xreg (r : reg_t) (x : xreg_t) :
  to_var r <> to_var x.
Proof. move=> [] hsize _; apply/eqP/reg_size_neq_xreg_size:hsize. Qed.

Lemma to_var_regx_neq_xreg (r : regx_t) (x : xreg_t) :
  to_var r <> to_var x.
Proof. move=> [] hsize _; apply/eqP/reg_size_neq_xreg_size:hsize. Qed.

Definition var_of_implicit_arg (i : implicit_arg) : var :=
  match i with
  | IArflag r => to_var r
  | IAreg r => to_var r
  end.

Definition sopn_constrained_register acr :=
  match acr with
  | ACR_any      => sopn.ACR_any
  | ACR_exact x  => sopn.ACR_exact (to_var x)
  | ACR_vector x => sopn.ACR_exact (to_var x)
  | ACR_subset s => sopn.ACR_subset (map to_var s)
  end.

Definition sopn_arg_desc (ad:arg_desc) :=
  match ad with
  | ADImplicit ia => sopn.ADImplicit (var_of_implicit_arg ia)
  | ADExplicit _ n ox => sopn.ADExplicit n (sopn_constrained_register ox)
  end.

End ARCH.

(* Extra ops are non-existing architecture-specific asm instructions that we
 * replace by real asm instructions during the asmgen pass.
 *)
Class asm_extra (reg regx xreg rflag cond asm_op extra_op : Type) :=
  { _asm   : asm reg regx xreg rflag cond asm_op
  ; _atoI  : arch_toIdent
  ; _extra : asmOp extra_op (* description of extra ops *)
  (* How to compile extra ops into a assembly instructions. *)
  ; to_asm :
    instr_info
    -> extra_op
    -> lexprs
    -> rexprs
    -> cexec (seq (asm_op_msb_t * lexprs * rexprs))
  }.

#[global]
Existing Instances _asm _atoI _extra.

Definition extra_op_t {reg regx xreg rflag cond asm_op extra_op} {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op} := extra_op.

Section AsmOpI.

Context `{asm_e : asm_extra}.

Variant extended_op :=
  | BaseOp of asm_op_msb_t
  | ExtOp of extra_op_t.

Definition extended_op_beq o1 o2 :=
  match o1, o2 with
  | BaseOp o1, BaseOp o2 => o1 == o2 :> _ * ceqT_eqType
  | ExtOp o1, ExtOp o2 => o1 == o2 ::>
  | _, _               => false
  end.

Lemma extended_op_eq_axiom : Equality.axiom extended_op_beq.
Proof.
  by case=> [] o1 [] o2 /=; (constructor || apply: reflect_inj eqP => ?? []).
Qed.

HB.instance Definition _ := hasDecEq.Build extended_op extended_op_eq_axiom.

Lemma atype_of_ltypeP : eval_ltype =1 eval_atype \o atype_of_ltype.
Proof. by case. Qed.

(* Sadly, the sumbool decidable equalities generated by elpi.derive are not
   transparent enough. We want them to reduce to [left erefl] when applied to
   concrete arguments (for the sake of convenience), and this is not the case
   of the generated ones.
   We redefine them manually, to ensure they reduce appropriately.
*)
Definition wsize_eq_dec (ws1 ws2 : wsize) : {ws1=ws2}+{ws1<>ws2}.
Proof.
  by case: ws1; case: ws2; try (right; discriminate); left; reflexivity.
Defined.

Definition ctype_eq_dec (ty1 ty2 : ctype) : {ty1=ty2}+{ty1<>ty2}.
Proof.
  case: ty1; case: ty2; try (right; discriminate).
  + by left; reflexivity.
  + by left; reflexivity.
  + move=> p1 p2.
    case: (Pos.eq_dec p1 p2).
    + by left; congruence.
    + by right; congruence.
  move=> ws1 ws2.
  case: (wsize_eq_dec ws1 ws2).
  + by left; congruence.
  by right; congruence.
Defined.

(* from https://systemf.epfl.ch/blog/computing-with-opaque-proofs/ *)
Definition computational_eq {m n} (opaque_eq: m = n) : m = n :=
  match List.list_eq_dec ctype_eq_dec m n with
  | left transparent_eq => transparent_eq
  | _ => opaque_eq (* dead code; could use [False_rect] *)
  end.

(* When it does not evaluate directly to [erefl], e.g. when the arguments are
   not fully concrete, we rely on this rewrite lemma to unblock computation. *)
Lemma computational_eq_refl n (e : n = n) : computational_eq e = erefl.
Proof.
  by apply (Eqdep_dec.UIP_dec (List.list_eq_dec ctype_eqb_OK_sumbool)).
Qed.

Definition semi_to_atype {tin tout} (semi: sem_prod (map eval_ltype tin) (exec (sem_tuple (map eval_ltype tout)))) :
    sem_prod (map eval_atype (map atype_of_ltype tin)) (exec (sem_tuple (map eval_atype (map atype_of_ltype tout)))) :=
  let eq l := computational_eq (etrans (eq_map atype_of_ltypeP _) (map_comp eval_atype atype_of_ltype l)) in
  ecast l (sem_prod l _) (eq tin) (ecast l (sem_prod _ (exec (sem_tuple l))) (eq tout) semi).

Lemma is_not_carr_ltype (tin : seq ltype) :
  all is_not_carr (map eval_atype (map atype_of_ltype tin)).
Proof.
  elim: tin => [//|ty tys /= ->].
  by case: ty.
Qed.

Lemma semi_to_atype_safe_wf tin safe :
  all (fun sc : safe_cond => ssrnat.leq (sc_needed_args sc) (size tin)) safe ->
  all (fun sc : safe_cond => ssrnat.leq (sc_needed_args sc) (size (map atype_of_ltype tin))) safe.
Proof. by rewrite size_map. Qed.

Lemma semi_to_atype_errty tin tout (semi: sem_prod (map eval_ltype tin) (exec (sem_tuple (map eval_ltype tout)))) :
  sem_forall (fun r => r <> Error ErrType) (map eval_ltype tin) semi ->
  sem_forall (fun r => r <> Error ErrType) (map eval_atype (map atype_of_ltype tin)) (semi_to_atype semi).
Proof.
  rewrite /semi_to_atype.
  move: (computational_eq _) (computational_eq _) semi => e1 e2.
  by rewrite -> e1, -> e2.
Qed.

Lemma semi_to_atype_safe tin tout (semi: sem_prod (map eval_ltype tin) (exec (sem_tuple (map eval_ltype tout))))safe :
  interp_safe_cond_ty safe semi ->
  interp_safe_cond_ty safe (semi_to_atype semi).
Proof.
  rewrite /semi_to_atype.
  move: (computational_eq _) (computational_eq _) semi => e1 e2.
  by rewrite -> e1, -> e2.
Qed.

Definition get_instr_desc (o: extended_op) : instruction_desc :=
 match o with
 | BaseOp o =>
   let id := instr_desc o in
   {| str      := id.(id_str_jas)
    ; tin      := map atype_of_ltype id.(id_tin)
    ; i_in     := map sopn_arg_desc id.(id_in)
    ; i_out    := map sopn_arg_desc id.(id_out)
    ; conflicts:= [::]
    ; tout     := map atype_of_ltype id.(id_tout)
    ; semi     := semi_to_atype id.(id_semi)
    ; semu     := @vuincl_app_sopn_v _ _ _ (is_not_carr_ltype _)
    ; i_safe   := id.(id_safe)
    ; i_init   := id.(id_init)
    ; i_valid  := id.(id_valid)
    ; i_safe_wf := semi_to_atype_safe_wf id.(id_safe_wf)
    ; i_semi_errty := fun h => semi_to_atype_errty (id.(id_semi_errty) h)
    ; i_semi_safe := fun h => semi_to_atype_safe (id.(id_semi_safe) h)
   |}
 | ExtOp o => asm_op_instr o
 end.

Definition sopn_prim_string_base (o : seq (string * prim_constructor asm_op)) :=
  let to_ex o := BaseOp (None, o) in
  map (fun '(s, p) => (s, map_prim_constructor to_ex p)) o.
Definition sopn_prim_string_extra (o : seq (string * prim_constructor extra_op)) :=
  let to_ex o := ExtOp o in
  map (fun '(s, p) => (s, map_prim_constructor to_ex p)) o.

Definition get_prime_op : seq (string * prim_constructor extended_op) :=
  sopn_prim_string_base prim_string ++ sopn_prim_string_extra sopn.prim_string.

Instance eqTC_extended_op : eqTypeC extended_op :=
  { ceqP := extended_op_eq_axiom }.

Global Instance asm_opI : asmOp extended_op :=
  { sopn.asm_op_instr := get_instr_desc;
    sopn.prim_string := get_prime_op }.

End AsmOpI.
