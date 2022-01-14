(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import utils oseq strings word memory_model global Utf8 Relation_Operators sem_type label.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
(* String representation of architecture components.
 * ToString is a class for types that have a string representation and a
 * particular stype, such as registers (represented as "RAX", "RSP", etc.
 * with sword U64 being the associated stype) or flags (represented as "CF",
 * "ZF", with sbool the associated stype).
 *)
Class ToString (t: stype) (T: Type) :=
  { category      : string    (* Name of the "register" used to print errors. *)
  ; _finC         :> finTypeC T
  ; to_string     : T -> string
  ; strings       : list (string * T)
  ; inj_to_string : injective to_string
  ; stringsE      : strings = [seq (to_string x, x) | x <- enum cfinT_finType]
  }.

Definition rtype {t T} `{ToString t T} := t.


(* -------------------------------------------------------------------- *)
(* Basic architecture declaration.
 * Parameterized by types for registers, extra registers, flags, conditions,
 * and shifts.
 *)
Class arch_decl (reg regx xreg rflag cond : Type) :=
  { reg_size : wsize     (* Register size. Also used as pointer size. *)
  ; xreg_size : wsize    (* Extended registers size. *)
  ; cond_eqC :> eqTypeC cond
  ; toS_r :> ToString (sword reg_size) reg
  ; toS_rx :> ToString (sword reg_size) regx
  ; toS_x :> ToString (sword xreg_size) xreg
  ; toS_f :> ToString sbool rflag
  ; reg_size_neq_xreg_size : reg_size != xreg_size
  ; callee_saved : seq reg
  ; ad_rsp : reg
  ; inj_toS_reg_regx : forall (r:reg) (rx:regx), to_string r <> to_string rx
  }.

Instance arch_pd `{arch_decl} : PointerData := { Uptr := reg_size }.

Definition mk_ptr `{arch_decl} name :=
  {| vtype := sword Uptr; vname := name; |}.

(* FIXME ARM : Try to not use this projection *)
Definition reg_t   {reg regx xreg rflag cond} `{arch : arch_decl reg regx xreg rflag cond} := reg.
Definition regx_t  {reg regx xreg rflag cond} `{arch : arch_decl reg regx xreg rflag cond} := regx.
Definition xreg_t  {reg regx xreg rflag cond} `{arch : arch_decl reg regx xreg rflag cond} := xreg.
Definition rflag_t {reg regx xreg rflag cond} `{arch : arch_decl reg regx xreg rflag cond} := rflag.
Definition cond_t  {reg regx xreg rflag cond} `{arch : arch_decl reg regx xreg rflag cond} := cond.

Definition wreg {reg xreg rflag cond} `{arch : arch_decl reg xreg rflag cond} :=
  sem_t (sword reg_size).

Definition wxreg {reg xreg rflag cond} `{arch : arch_decl reg xreg rflag cond} :=
  sem_t (sword xreg_size).

Section DECL.

Context {reg regx xreg rflag cond} `{arch : arch_decl reg regx xreg rflag cond}.

Lemma sword_reg_neq_xreg :
  sword reg_size != sword xreg_size.
Proof.
  apply/eqP. move=> []. apply/eqP. exact: reg_size_neq_xreg_size.
Qed.

(* -------------------------------------------------------------------- *)
(* Addresses.
 * An address consists of
 *   - A displacement (an immediate value).
 *   - A base (a register).
 *   - A scale.
 *   - An offset (a register).
 * The effective address is displacement + base + offset * scale.
 *)
Record reg_address : Type := mkAddress
  { ad_disp   : pointer
  ; ad_base   : option reg_t
  ; ad_scale  : nat
  ; ad_offset : option reg_t
  }.

Inductive address :=
| Areg of reg_address (* Absolute address. *)
| Arip of pointer.    (* Address relative to instruction pointer. *)

Definition oeq_reg (x y:option reg_t) :=
  @eq_op (option_eqType ceqT_eqType) x y.

Definition reg_address_beq (addr1: reg_address) addr2 :=
  match addr1, addr2 with
  | mkAddress d1 b1 s1 o1, mkAddress d2 b2 s2 o2 =>
    [&& d1 == d2, oeq_reg b1 b2, s1 == s2 & oeq_reg o1 o2]
  end.

Lemma reg_address_eq_axiom : Equality.axiom reg_address_beq.
Proof.
case=> [d1 b1 s1 o1] [d2 b2 s2 o2]; apply: (iffP idP) => /=.
+ by case/and4P ; do 4! move/eqP=> ->.
by case; do 4! move=> ->; rewrite /oeq_reg !eqxx.
Qed.

Definition reg_address_eqMixin := Equality.Mixin reg_address_eq_axiom.
Canonical reg_address_eqType := EqType reg_address reg_address_eqMixin.

(* -------------------------------------------------------------------- *)

Definition address_beq (addr1: address) addr2 :=
  match addr1, addr2 with
  | Areg ra1, Areg ra2 => ra1 == ra2
  | Arip p1, Arip p2   => p1 == p2
  | _, _ => false
  end.

Lemma address_eq_axiom : Equality.axiom address_beq.
Proof.
  by case=> []? []? /=; (constructor || apply: reflect_inj eqP => ?? []).
Qed.

Definition address_eqMixin := Equality.Mixin address_eq_axiom.
Canonical address_eqType := EqType address address_eqMixin.

(* -------------------------------------------------------------------- *)
(* Arguments to assembly instructions. *)
Variant asm_arg : Type :=
| Condt  of cond_t
| Imm ws of word ws
| ImmZ   of Z        (* FIXME: unify with Imm. *)
| Reg    of reg_t
| Regx   of regx_t
| Addr   of address
| XReg   of xreg_t.

Definition asm_args := (seq asm_arg).

Definition asm_arg_beq (a1 a2:asm_arg) :=
  match a1, a2 with
  | Condt t1, Condt t2 => t1 == t2 ::>
  | Imm sz1 w1, Imm sz2 w2 => (sz1 == sz2) && (wunsigned w1 == wunsigned w2)
  | ImmZ z1, ImmZ z2 => z1 == z2
  | Reg r1, Reg r2     => r1 == r2 ::>
  | Regx r1, Regx r2   => r1 == r2 ::>
  | Addr a1, Addr a2   => a1 == a2
  | XReg r1, XReg r2   => r1 == r2 ::>
  | _, _ => false
  end.

Definition Imm_inj sz sz' w w' (e: @Imm sz w = @Imm sz' w') :
  ∃ e : sz = sz', eq_rect sz (λ s, (word s)) w sz' e = w' :=
  let 'Logic.eq_refl := e in (ex_intro _ erefl erefl).

Lemma asm_arg_eq_axiom : Equality.axiom asm_arg_beq.
Proof.
  case => [?| sz1 w1 |?|?|?|?|?] [?| sz2 w2 |?|?|?|?|?] /=;
    try by (constructor || apply: reflect_inj eqP => ?? []).
  apply: (iffP idP) => //=.
  + by move=> /andP [] /eqP ? /eqP; subst => /wunsigned_inj ->.
  by move=> /Imm_inj [? ];subst => /= ->;rewrite !eqxx.
Qed.

Definition asm_arg_eqMixin := Equality.Mixin asm_arg_eq_axiom.
Canonical asm_arg_eqType := EqType asm_arg asm_arg_eqMixin.

(* -------------------------------------------------------------------- *)
(* Writing a large word to register or memory
 * When writing to a register, depending on the instruction,
 * the most significant bits are either preserved or cleared.
 *)
Variant msb_flag : Type :=
| MSB_CLEAR
| MSB_MERGE.

Scheme Equality for msb_flag.

Lemma msb_flag_eq_axiom : Equality.axiom msb_flag_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_msb_flag_dec_bl.
  by apply: internal_msb_flag_dec_lb.
Qed.

Definition msb_flag_eqMixin := Equality.Mixin msb_flag_eq_axiom.
Canonical msb_flag_eqType := EqType msb_flag msb_flag_eqMixin.

(* -------------------------------------------------------------------- *)
(* Implicit arguments.
 * Assembly instructions may have implicit arguments, such as flags if
 * they are set by the instruction.
 *)
Variant implicit_arg : Type :=
| IArflag of rflag_t  (* Implicit flag. *)
| IAreg   of reg_t.   (* Implicit register. *)

Definition implicit_arg_beq (i1 i2 : implicit_arg) :=
  match i1, i2 with
  | IArflag f1, IArflag f2 => f1 == f2 ::>
  | IAreg r1, IAreg r2 => r1 == r2 ::>
  | _, _ => false
  end.

Lemma implicit_arg_eq_axiom : Equality.axiom implicit_arg_beq.
Proof.
  by case=> []? []? /=; (constructor || apply: reflect_inj eqP => ?? []).
Qed.

Definition implicit_arg_eqMixin := Equality.Mixin implicit_arg_eq_axiom.
Canonical implicit_arg_eqType := EqType _ implicit_arg_eqMixin.

(* -------------------------------------------------------------------- *)
(* Address kinds.
 * An address argument may be used in two ways:
 * - To compute the effective address (such as in LEA in x86, or ADR in ARMv7).
 * - To load data from memory.
 *)
Variant addr_kind : Type :=
| AK_compute (* Only compute the address. *)
| AK_mem.    (* Compute the address and load from memory. *)

Scheme Equality for addr_kind.

Lemma addr_kind_eq_axiom : Equality.axiom addr_kind_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_addr_kind_dec_bl.
  by apply: internal_addr_kind_dec_lb.
Qed.

Definition addr_kind_eqMixin := Equality.Mixin addr_kind_eq_axiom.
Canonical addr_kind_eqType := EqType _ addr_kind_eqMixin.

(* -------------------------------------------------------------------- *)
(* Argument description.
 * An argument may be either implicit or explicit.
 *)
Variant arg_desc :=
| ADImplicit of implicit_arg
| ADExplicit
    of addr_kind      (* If argument is an address, should it be loaded? *)
     & nat            (* Position of the argument in assembly syntax. *)
     & option reg_t.  (* Set if there is only one valid register. *)

Definition arg_desc_beq (d1 d2 : arg_desc) :=
  match d1, d2 with
  | ADImplicit i1, ADImplicit i2 => i1 == i2
  | ADExplicit k1 n1 or1, ADExplicit k2 n2 or2 =>
    (k1 == k2) && (n1 == n2) && (or1 == or2 :> option_eqType ceqT_eqType)
  | _, _ => false
  end.

Lemma arg_desc_eq_axiom : Equality.axiom arg_desc_beq.
Proof.
  case=> [i1|k1 n1 or1] [i2|k2 n2 or2] /=;
    try by (constructor || apply: reflect_inj eqP => ?? []).
  do! (case: eqP; try by constructor; congruence).
Qed.

Definition arg_desc_eqMixin := Equality.Mixin arg_desc_eq_axiom.
Canonical  arg_desc_eqType  := EqType arg_desc arg_desc_eqMixin.

Definition F  f   := ADImplicit (IArflag f).
Definition R  r   := ADImplicit (IAreg   r).
Definition E  n   := ADExplicit AK_mem n None.
Definition Ec n   := ADExplicit AK_compute n None.
Definition Ef n r := ADExplicit AK_mem n (Some  r).

Definition check_oreg or ai :=
  match or, ai with
  | Some r, Reg r'  => r == r' ::>
  | Some _, Imm _ _ => true
  | Some _, _       => false
  | None, _         => true
  end.

(* -------------------------------------------------------------------- *)
(* Argument kinds.
 * Types for arguments of assembly instructions.
 *)
Variant arg_kind :=
| CAcond
| CAreg
| CAregx
| CAxmm
| CAmem of bool (* true if Global is allowed *)
| CAimm of wsize
| CAimmZ.

Scheme Equality for arg_kind.

Lemma arg_kind_eq_axiom : Equality.axiom arg_kind_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_arg_kind_dec_bl.
  by apply: internal_arg_kind_dec_lb.
Qed.

Definition arg_kind_eqMixin := Equality.Mixin arg_kind_eq_axiom.
Canonical  arg_kind_eqType  := EqType _ arg_kind_eqMixin.


(* An argument position where different argument kinds are allowed is
 * represented by a list of these kinds.
 * For instance, a position taking a register or an immediate is represented
 * by [:: CAreg; CAimm ] : arg_kinds.
 * This is a disjunction of the possible kinds for a position.
*)
Definition arg_kinds := seq arg_kind.

(* Each argument position has a description.
 * For instance [:: a0; a1; a2 ] is a description where the first argument
 * is described by the arg_kind a0, the second by a1 and the third by a2.
 * This is a conjunction of argument descriptions.
 *)
Definition args_kinds := seq arg_kinds.

(* An assembly instruction may take different number of arguments.
 * For instance, an instruction may take two registers, add their values
 * and write to the first, or take three registers, add two and store the
 * result to the third.
 * This is a disjunction of these signatures.
 *)
Definition i_args_kinds := seq args_kinds.

Definition check_arg_kind (a:asm_arg) (cond: arg_kind) :=
  match a, cond with
  | Condt _, CAcond => true
  | Imm sz _, CAimm sz' => sz == sz'
  | ImmZ _, CAimmZ => true
  | Reg _, CAreg => true
  | Regx _, CAregx => true
  | Addr _, CAmem _ => true
  | XReg _, CAxmm   => true
  | _, _ => false
  end.

Definition check_arg_kinds (a:asm_arg) (cond:arg_kinds) :=
  has (check_arg_kind a) cond.

Definition check_args_kinds (a:asm_args) (cond:args_kinds) :=
 all2 check_arg_kinds a cond.

Definition check_i_args_kinds (cond:i_args_kinds) (a:asm_args) :=
  has (check_args_kinds a) cond.

Definition check_arg_dest (ad:arg_desc) (ty:stype) :=
  match ad with
  | ADImplicit _ => true
  | ADExplicit _ _ _ => ty != sbool
  end.

(* -------------------------------------------------------------------- *)
Variant pp_asm_op_ext :=
  | PP_error
  | PP_name
  | PP_iname   of wsize
  | PP_iname2  of string & wsize & wsize
  | PP_viname  of velem & bool (* long *)
  | PP_viname2 of velem & velem (* source and target element sizes *)
  | PP_ct      of asm_arg.

Record pp_asm_op := mk_pp_asm_op {
  pp_aop_name : string;
  pp_aop_ext  : pp_asm_op_ext;
  pp_aop_args : seq (wsize * asm_arg);
}.

(* -------------------------------------------------------------------- *)
(* Instruction descriptions. *)
Record instr_desc_t := {
  (* Info for architecture semantics. *)
  (* When writing a smaller value to a register, keep or clear old bits? *)
  id_msb_flag   : msb_flag;
  (* Types of input arguments. *)
  id_tin        : seq stype;
  (* Description of input arguments. *)
  id_in         : seq arg_desc;
  (* Types of output arguments. *)
  id_tout       : seq stype;
  (* Description of output arguments. *)
  id_out        : seq arg_desc;
  (* Semantics (only deals with values). *)
  id_semi       : sem_prod id_tin (exec (sem_tuple id_tout));
  (* Possible signatures for an instruction. *)
  id_args_kinds : i_args_kinds;
  (* Number of explicit arguments in assembly syntax. *)
  id_nargs      : nat;
  (* Info for jasmin *)
  id_eq_size    : (size id_in == size id_tin) && (size id_out == size id_tout);
  id_tin_narr   : all is_not_sarr id_tin;
  id_tout_narr  : all is_not_sarr id_tout;
  id_str_jas    : unit -> string;
  id_check_dest : all2 check_arg_dest id_out id_tout;
  id_safe       : seq safe_cond;
  id_wsize      : wsize;
  id_pp_asm     : asm_args -> pp_asm_op;
}.

(* -------------------------------------------------------------------- *)
Variant prim_constructor (asm_op:Type) :=
  | PrimP of wsize & (wsize -> asm_op)
  | PrimM of asm_op
  | PrimV of (velem -> wsize -> asm_op)
  | PrimSV of (signedness -> velem -> wsize -> asm_op)
  | PrimX of (wsize -> wsize -> asm_op)
  | PrimVV of (velem → wsize → velem → wsize → asm_op)
  .

(* -------------------------------------------------------------------- *)
(* Architecture operand declaration. *)
Class asm_op_decl (asm_op: Type) :=
  { _eqT          :> eqTypeC asm_op
  ; instr_desc_op : asm_op -> instr_desc_t
  ; prim_string   : list (string * prim_constructor asm_op)
  }.

Definition asm_op_t' {asm_op} {asm_op_d : asm_op_decl asm_op} := asm_op.
(* We extend [asm_op] in order to deal with msb flags *)
Definition asm_op_msb_t {asm_op} {asm_op_d : asm_op_decl asm_op} := (option wsize * asm_op)%type.

Context `{asm_op_d : asm_op_decl}.

Definition extend_size (ws: wsize) (t:stype) :=
  match t with
  | sword ws' => if (ws' <= ws)%CMP then sword ws else sword ws'
  | _ => t
  end.

Definition wextend_size (ws: wsize) (t:stype) : sem_ot t -> sem_ot (extend_size ws t) :=
  match t return sem_ot t -> sem_ot (extend_size ws t) with
  | sword ws' =>
    fun (w: word ws') =>
    match (ws' <= ws)%CMP as b return sem_ot (if b then sword ws else sword ws') with
    | true => zero_extend ws w
    | false => w
    end
  | _ => fun x => x
  end.

Fixpoint extend_tuple (ws:wsize) (id_tout : list stype) (t: sem_tuple id_tout) :
   sem_tuple (map (extend_size ws) id_tout) :=
 match id_tout return sem_tuple id_tout -> sem_tuple (map (extend_size ws) id_tout) with
 | [::] => fun _ => tt
 | t :: ts =>
   match ts return
     (sem_tuple ts -> sem_tuple (map (extend_size ws) ts)) ->
     sem_tuple (t::ts) -> sem_tuple (map (extend_size ws) (t::ts)) with
   | [::] => fun rec_ x => wextend_size ws x
   | t'::ts'    => fun rec_ p => (wextend_size ws p.1, rec_ p.2)
   end (@extend_tuple ws ts)
 end t.

Fixpoint apply_lprod (A B : Type) (f : A -> B) (ts:list Type) : lprod ts A -> lprod ts B :=
  match ts return lprod ts A -> lprod ts B with
  | [::] => fun a => f a
  | t :: ts' => fun g x => apply_lprod f (g x)
  end.

Lemma instr_desc_aux1 ws (id_in id_out : list arg_desc) (id_tin id_tout : list stype) :
  is_true ((size id_in == size id_tin) && (size id_out == size id_tout)) ->
  is_true ((size id_in == size id_tin) && (size id_out == size (map (extend_size ws) id_tout))).
Proof. by rewrite size_map. Qed.

Lemma instr_desc_aux2 ws (id_out : list arg_desc) (id_tout : list stype) :
  is_true (all2 check_arg_dest id_out id_tout) ->
  is_true (all2 check_arg_dest id_out (map (extend_size ws) id_tout)).
Proof.
  rewrite /is_true => <-.
  elim: id_out id_tout => [ | a id_out hrec] [ | t id_tout] //=.
  rewrite hrec; case: t => // ws'.
  by rewrite /extend_size /check_arg_dest; case: a => //; case: ifP.
Qed.

Definition is_not_CAmem (cond : arg_kind) :=
  match cond with
  | CAmem _ => false
  | _ => true
  end.

Definition exclude_mem_args_kinds (d : arg_desc) (cond : args_kinds) :=
  match d with
  | ADExplicit _ i _ =>
    mapi (fun k c => if k == i then filter is_not_CAmem c else c) cond
  | _ => cond
  end.

Definition exclude_mem_i_args_kinds (d : arg_desc) (cond : i_args_kinds) : i_args_kinds :=
  map (exclude_mem_args_kinds d) cond.

(* Remark: if the cast is explicit and do nothing then this code will reject store in memory
   while assembly accepts it.
   It is our choice... *)

Definition exclude_mem_aux (cond : i_args_kinds) (d : seq arg_desc) :=
  foldl (fun cond d => exclude_mem_i_args_kinds d cond) cond d.

Definition exclude_mem (cond : i_args_kinds) (d : seq arg_desc) : i_args_kinds :=
  filter (fun c => [::] \notin c) (exclude_mem_aux cond d).

Lemma instr_desc_tout_narr ws xs :
  all is_not_sarr xs -> all is_not_sarr (map (extend_size ws) xs).
Proof.
  apply all_map'.
  move=> [] //= ws'.
  by case: (ws' <= ws)%CMP.
Qed.

(* An extension of [instr_desc] that deals with msb flags *)
Definition instr_desc (o:asm_op_msb_t) : instr_desc_t :=
  let (ws, o) := o in
  let d := instr_desc_op o in
  if ws is Some ws then
    if d.(id_msb_flag) == MSB_CLEAR then
    {| id_msb_flag   := d.(id_msb_flag);
       id_tin        := d.(id_tin);
       id_in         := d.(id_in);
       id_tout       := map (extend_size ws) d.(id_tout);
       id_out        := d.(id_out);
       id_semi       :=
         apply_lprod (Result.map (@extend_tuple ws d.(id_tout))) d.(id_semi);
       id_args_kinds := exclude_mem d.(id_args_kinds) d.(id_out) ;
       id_nargs      := d.(id_nargs);
       id_eq_size    := instr_desc_aux1 ws d.(id_eq_size);
       id_tin_narr   := d.(id_tin_narr);
       id_tout_narr  := instr_desc_tout_narr _ d.(id_tout_narr);
       id_str_jas    := d.(id_str_jas);
       id_check_dest := instr_desc_aux2 ws d.(id_check_dest);
       id_safe       := d.(id_safe);
       id_wsize      := d.(id_wsize);
       id_pp_asm     := d.(id_pp_asm); |}
    else d (* FIXME do the case for MSB_KEEP *)
  else
    d.

(* -------------------------------------------------------------------- *)
(* Assembly language. *)
Variant asm_i : Type :=
  | ALIGN
  | LABEL of label
  | STORELABEL of reg_t & label (* Store the address of a local label *)
  (* Jumps *)
  | JMP    of remote_label (* Direct jump *)
  | JMPI   of asm_arg (* Indirect jump *)
  | Jcc    of label & cond_t  (* Conditional jump *)
  (* Functions *)
  | JAL of reg_t & remote_label (* Direct jump; return address is saved in a register *)
  | CALL of remote_label (* Direct jump; return address is saved at the top of the stack *)
  | POPPC (* Pop a destination from the stack and jump there *)
  (* Instructions exposed at source-level *)
  | AsmOp  of asm_op_t' & asm_args.

Definition asm_code := seq asm_i.

(* Any register, used for function arguments and returned values. *)
Variant asm_typed_reg :=
  | ARReg of reg_t
  | ARegX of regx_t
  | AXReg of xreg_t
  | ABReg of rflag_t.

Notation asm_typed_regs := (seq asm_typed_reg).

Record asm_fundef := XFundef
  { asm_fd_align : wsize
  ; asm_fd_arg   : asm_typed_regs
  ; asm_fd_body  : asm_code
  ; asm_fd_res   : asm_typed_regs
  ; asm_fd_export: bool
  ; asm_fd_total_stack: Z
  }.

Record asm_prog : Type :=
  { asm_globs : seq u8
  ; asm_funcs : seq (funname * asm_fundef)
  }.

End DECL.

Section ENUM.
  Context `{arch : arch_decl}.

  Definition registers : seq reg_t := cenum.

  Definition registerxs : seq regx_t := cenum.

  Definition xregisters : seq xreg_t := cenum.

  Definition rflags : seq rflag_t := cenum.
End ENUM.

(* -------------------------------------------------------------------- *)
(* Flag values. *)
Variant rflagv := Def of bool | Undef.
Scheme Equality for rflagv.

Lemma rflagv_eq_axiom : Equality.axiom rflagv_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_rflagv_dec_bl.
  by apply: internal_rflagv_dec_lb.
Qed.

Definition rflagv_eqMixin := Equality.Mixin rflagv_eq_axiom.
Canonical rflagv_eqType := EqType _ rflagv_eqMixin.

(* -------------------------------------------------------------------- *)
(* Assembly declaration. *)

Class asm (reg regx xreg rflag cond asm_op: Type) :=
  { _arch_decl   :> arch_decl reg regx xreg rflag cond
  ; _asm_op_decl :> asm_op_decl asm_op
  ; eval_cond   : (rflag_t -> exec bool) -> cond_t -> exec bool
  ; stack_pointer_register : reg_t
  }.
