(* ** License
 * -----------------------------------------------------------------------
 * Copyright 2016--2017 IMDEA Software Institute
 * Copyright 2016--2017 Inria
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ----------------------------------------------------------------------- *)


(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import utils oseq strings wsize memory_model global Utf8 Relation_Operators sem_type syscall label.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ==================================================================== *)
Class ToString (t:stype) (T:Type) := 
  { category      : string          (* name of the "register" used to print error *) 
  ; _finC         :> finTypeC T
  ; to_string     : T -> string
  ; strings       : list (string * T)
  ; inj_to_string : injective to_string
  ; stringsE      : strings = [seq (to_string x, x) | x <- enum cfinT_finType]
  }.

Definition rtype {t T} `{ToString t T} := t.

Section Section.

Context `{tS : ToString}.

Definition of_string (s : string) :=
  assoc strings s.

(* -------------------------------------------------------------------- *)
Lemma in_enum (r:T) : r \in enum cfinT_finType.
Proof. apply (mem_enum (T:=cfinT_finType)). Qed.
Hint Resolve in_enum : core.

Lemma to_stringK : pcancel to_string of_string.
Proof.
move=> r; rewrite /of_string stringsE; apply /(@assocP _ ceqT_eqType).
+ rewrite -map_comp (map_inj_uniq (T1:=ceqT_eqType)) //.
  + by apply: (enum_uniq (T:=cfinT_finType)).
  by apply inj_to_string.
by apply: (map_f (T1:=ceqT_eqType) (T2:=prod_eqType _ ceqT_eqType)).
Qed.

(* -------------------------------------------------------------------- *)

Lemma of_stringI s r : of_string s = Some r -> to_string r = s.
Proof.
  have h := to_stringK r.
  apply : (assoc_inj (U:= ceqT_eqType) _ h).
  by rewrite stringsE -map_comp (map_inj_uniq (T1:=ceqT_eqType)) ?(enum_uniq (T:=cfinT_finType)).
Qed.

Lemma inj_of_string s1 s2 r :
     of_string s1 = Some r
  -> of_string s2 = Some r
  -> s1 = s2.
Proof. by move=> /of_stringI <- /of_stringI <-. Qed.

(* -------------------------------------------------------------------- *)
Definition to_var r :=
  {| vtype := rtype; vname := to_string r |}.

Definition of_var (v:var) :=
  if v.(vtype) == rtype then of_string v.(vname)
  else None.

Lemma of_varP v r : of_var v = Some r <-> v.(vtype) = rtype /\ of_string v.(vname) = Some r.
Proof. by rewrite /of_var; split=> [ | []/eqP -> ?]; first case: eqP. Qed.

Lemma to_varK : pcancel to_var of_var.
Proof. by move=> ?; rewrite /to_var /of_var /= eq_refl to_stringK. Qed.

Lemma inj_to_var : injective to_var.
Proof. apply: pcan_inj to_varK. Qed.
Global Arguments inj_to_var {_ _}.

Lemma of_varI {v r} : of_var v = Some r -> to_var r = v.
Proof.
  rewrite /of_var /= /to_var; case: eqP => // heq /of_stringI.
  by case: v heq => /= ?? -> <-.
Qed.

Lemma inj_of_var {v1 v2 r} : of_var v1 = Some r -> of_var v2 = Some r -> v1 = v2.
Proof. by move=> /of_varI <- /of_varI <-. Qed.

End Section.

Hint Resolve in_enum : core.
(* ==================================================================== *)

Class arch_decl (reg xreg rflag cond : Type) := 
  { reg_size  : wsize (* [reg_size] is also used as the size of pointers *)
  ; xreg_size : wsize
  ; cond_eqC  :> eqTypeC cond
  ; toS_r     :> ToString (sword reg_size) reg
  ; toS_x     :> ToString (sword xreg_size) xreg
  ; toS_f     :> ToString sbool rflag
}.

Instance arch_pd {reg xreg rflag cond} {arch : arch_decl reg xreg rflag cond} : PointerData := 
  { Uptr := reg_size }.

(* FIXME ARM : Try to not use this projection *)
Definition reg_t    {reg xreg rflag cond} {arch : arch_decl reg xreg rflag cond} := reg.
Definition xreg_t   {reg xreg rflag cond} {arch : arch_decl reg xreg rflag cond} := xreg.
Definition rflag_t  {reg xreg rflag cond} {arch : arch_decl reg xreg rflag cond} := rflag.
Definition cond_t   {reg xreg rflag cond} {arch : arch_decl reg xreg rflag cond} := cond.

Definition wreg  {reg xreg rflag cond} {arch : arch_decl reg xreg rflag cond} := sem_t (sword reg_size).
Definition wxreg {reg xreg rflag cond} {arch : arch_decl reg xreg rflag cond} := sem_t (sword xreg_size).

(* -------------------------------------------------------------------- *)

Module RegMap. Section Section.

  Context {reg xreg rflag cond} {arch : arch_decl reg xreg rflag cond}.

  Definition map := (* {ffun reg_t -> wreg}. *)
    FinMap.map (T:= reg_t) wreg.

  Definition set (m : map) (x : reg_t) (y : wreg) : map :=
    FinMap.set m x y.

End Section. End RegMap.

(* -------------------------------------------------------------------- *)

Module XRegMap. Section Section.

  Context {reg xreg rflag cond} {arch : arch_decl reg xreg rflag cond}.

  Definition map := (* {ffun xreg_t -> wxreg }. *)
    FinMap.map (T:= xreg_t) wxreg.

  Definition set (m : map) (x : xreg_t) (y : wxreg) : map :=
    FinMap.set m x y.

End Section. End XRegMap.

(* -------------------------------------------------------------------- *)

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

Module RflagMap. Section Section.

  Context {reg xreg rflag cond} {arch : arch_decl reg xreg rflag cond}.

  Definition map := (* {ffun rflag_t -> rflagv}. *)
    FinMap.map (T:= rflag_t) rflagv.

  Definition set (m : map) (x : rflag_t) (y : rflagv) : map :=
    FinMap.set m x y.

End Section. End RflagMap.

(* -------------------------------------------------------------------- *)
Notation regmap   := RegMap.map.
Notation xregmap  := XRegMap.map.
Notation rflagmap := RflagMap.map.

Section DECL.

Context {reg xreg rflag cond} {arch : arch_decl reg xreg rflag cond}.

Record asmmem : Type := AsmMem {
  asm_rip  : pointer; 
  asm_scs : syscall_state;                          
  asm_mem  : mem;
  asm_reg  : regmap;
  asm_xreg : xregmap;
  asm_flag : rflagmap;
}.

Class asm_syscall_sem := { eval_syscall : syscall_t -> asmmem -> exec asmmem }.

(* -------------------------------------------------------------------- *)
(* disp + base + scale × offset *)
Record reg_address : Type := mkAddress {
  ad_disp   : pointer;
  ad_base   : option reg_t;
  ad_scale  : nat;
  ad_offset : option reg_t;
}.

Variant address :=
  | Areg of reg_address
  | Arip of pointer.  
   
(* -------------------------------------------------------------------- *)

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

Definition rflags : list rflag := enum cfinT_finType.
Definition registers : list reg := enum cfinT_finType.
Definition xregisters : list xreg := enum cfinT_finType.

Variant asm_arg : Type :=
  | Condt  of cond_t
  | Imm ws of word ws
  | Reg    of reg_t
  | Addr   of address
  | XReg   of xreg_t.

Definition asm_args := (seq asm_arg).

Definition asm_arg_beq (a1 a2:asm_arg) :=
  match a1, a2 with
  | Condt t1, Condt t2 => t1 == t2 ::>
  | Imm sz1 w1, Imm sz2 w2 => (sz1 == sz2) && (wunsigned w1 == wunsigned w2)
  | Reg r1, Reg r2     => r1 == r2 ::>
  | Addr a1, Addr a2     => a1 == a2
  | XReg r1, XReg r2   => r1 == r2 ::>
  | _, _ => false
  end.

Definition Imm_inj sz sz' w w' (e: @Imm sz w = @Imm sz' w') :
  ∃ e : sz = sz', eq_rect sz (λ s, (word s)) w sz' e = w' :=
  let 'Logic.eq_refl := e in (ex_intro _ erefl erefl).

Lemma asm_arg_eq_axiom : Equality.axiom asm_arg_beq.
Proof.
  case => [t1 | sz1 w1 | r1 | a1 | xr1] [t2 | sz2 w2 | r2 | a2 | xr2] /=;
    try by (constructor || apply: reflect_inj eqP => ?? []).
  apply: (iffP idP) => //=.
  + by move=> /andP [] /eqP ? /eqP; subst => /wunsigned_inj ->.
  by move=> /Imm_inj [? ];subst => /= ->;rewrite !eqxx.
Qed.

Definition asm_arg_eqMixin := Equality.Mixin asm_arg_eq_axiom.
Canonical asm_arg_eqType := EqType asm_arg asm_arg_eqMixin.

(* -------------------------------------------------------------------- *)
(* Writing a large word to register or memory *)
(* When writing to a register, depending on the instruction,
  the most significant bits are either preserved or cleared. *)
Variant msb_flag := MSB_CLEAR | MSB_MERGE.
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

Variant implicit_arg : Type :=
  | IArflag of rflag_t
  | IAreg   of reg_t.

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

Variant addr_kind : Type :=
  | AK_compute (* Compute the address *)
  | AK_mem.    (* Compute the address and load from memory *)

Scheme Equality for addr_kind.

Lemma addr_kind_eq_axiom : Equality.axiom addr_kind_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_addr_kind_dec_bl.
  by apply: internal_addr_kind_dec_lb.
Qed.

Definition addr_kind_eqMixin := Equality.Mixin addr_kind_eq_axiom.
Canonical addr_kind_eqType := EqType _ addr_kind_eqMixin.

Variant arg_desc :=
| ADImplicit  of implicit_arg
| ADExplicit  of addr_kind & nat & option reg_t.

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
Definition Ec n := ADExplicit AK_compute n None.
Definition Ef n r := ADExplicit AK_mem n (Some  r).

Definition check_oreg or ai :=
  match or, ai with
  | Some r, Reg r'  => r == r' ::>
  | Some _, Imm _ _ => true
  | Some _, _       => false
  | None, _         => true
  end.

Variant arg_kind :=
  | CAcond
  | CAreg
  | CAxmm
  | CAmem of bool (* true if Global is allowed *)
  | CAimm of wsize
  .

Scheme Equality for arg_kind.

Lemma arg_kind_eq_axiom : Equality.axiom arg_kind_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_arg_kind_dec_bl.
  by apply: internal_arg_kind_dec_lb.
Qed.

Definition arg_kind_eqMixin := Equality.Mixin arg_kind_eq_axiom.
Canonical  arg_kind_eqType  := EqType _ arg_kind_eqMixin.

Definition arg_kinds := seq arg_kind.
Definition args_kinds := seq arg_kinds.
Definition i_args_kinds := seq args_kinds. (* disjunction of conjuction of disjunction *)

Definition check_arg_kind (a:asm_arg) (cond: arg_kind) :=
  match a, cond with
  | Condt _, CAcond => true
  | Imm sz _, CAimm sz' => sz == sz'
  | Reg _, CAreg => true
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

Record instr_desc_t := mk_instr_desc {
  (* Info for x86 sem *)
  id_msb_flag   : msb_flag;
  id_tin        : seq stype;
  id_in         : seq arg_desc;
  id_tout       : seq stype;
  id_out        : seq arg_desc;
  id_semi       : sem_prod id_tin (exec (sem_tuple id_tout));
  id_args_kinds : i_args_kinds;
  id_nargs      : nat;
  (* Info for jasmin *)
  id_eq_size    : (size id_in == size id_tin) && (size id_out == size id_tout);
  id_tin_narr   : all is_not_sarr id_tin;
  id_str_jas    : unit -> string;
  id_check_dest : all2 check_arg_dest id_out id_tout;
  id_safe       : seq safe_cond;
  id_wsize      : wsize;  (* ..... *)
  id_pp_asm     : asm_args -> pp_asm_op;
}.

Variant prim_constructor (asm_op:Type) :=
  | PrimP of wsize & (wsize -> asm_op)
  | PrimM of asm_op
  | PrimV of (velem -> wsize -> asm_op)
  | PrimSV of (signedness -> velem -> wsize -> asm_op)
  | PrimX of (wsize -> wsize -> asm_op)
  | PrimVV of (velem → wsize → velem → wsize → asm_op)
  .

Class asm_op_decl (asm_op : Type) := 
  { _eqT          :> eqTypeC asm_op
  ; instr_desc_op : asm_op -> instr_desc_t
  ; prim_string   : list (string * prim_constructor asm_op) }.

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
       id_str_jas    := d.(id_str_jas);
       id_check_dest := instr_desc_aux2 ws d.(id_check_dest);
       id_safe       := d.(id_safe);
       id_wsize      := d.(id_wsize);
       id_pp_asm     := d.(id_pp_asm); |}
    else d (* FIXME do the case for MSB_KEEP *)
  else
    d.

Variant asm_i : Type :=
  | ALIGN
  | LABEL of label
  | STORELABEL of reg_t & label (* Store the address of a local label *)
    (* Jumps *)
  | JMP    of remote_label (* Direct jump *)
  | JMPI   of asm_arg (* Indirect jump *)
  | Jcc    of label & cond_t  (* Conditional jump *)
  | AsmOp  of asm_op_t' & asm_args
  | SysCall of syscall_t.

Definition asm_code := seq asm_i.

Record asm_fundef := XFundef 
  { asm_fd_align : wsize
  ; asm_fd_arg   : asm_args   (* FIXME did we really want this *)
  ; asm_fd_body  : asm_code
  ; asm_fd_res   : asm_args   (* FIXME did we really want this *)
  ; asm_fd_export: bool  }.

Record asm_prog : Type :=
  { asm_globs : seq u8
  ; asm_funcs : seq (funname * asm_fundef) }.


(*
Inductive syscall_arg := 
  | SAreg  of reg_t
  | SAxreg of xreg_t.

Definition sca2var (a:syscall_arg) : var := 
  match a with
  | SAreg x => to_var x
  | SAxreg x => to_var x
  end.
*)

Class arch_syscall_info := {
   (* To define the Semantic *)
   syscall_sig_r : syscall_t -> seq reg_t * seq reg_t; (* FIXME : seq syscall_arg * seq syscall_arg; *)
   callee_saved_r : seq reg_t;                         (* FIXME it should be : seq syscall_arg;      *)
(*
   all_vars     : Sv.t;
   callee_saved : Sv.t;
   syscall_sigP : 
     forall o, (syscall_sig o).1 = map sca2var (syscall_sig_r o).1 /\
               (syscall_sig o).2 = map sca2var (syscall_sig_r o).2;
   callee_saveP : callee_saved = sv_of_list id (map sca2var callee_saved_r); 
*)
}.

End DECL.

Class asm (reg xreg rflag cond asm_op: Type) := 
  { _arch_decl   :> arch_decl reg xreg rflag cond
  ; _asm_op_decl :> asm_op_decl asm_op
  ; _asm_syscall :> asm_syscall_sem
  ; eval_cond    : (rflag_t -> result error bool) -> cond_t -> result error bool
  }.
