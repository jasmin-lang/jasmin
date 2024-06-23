From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype finfun.
From mathcomp Require Import ssralg word_ssrZ.
Require oseq.
Require Import ZArith
utils
strings
memory_model
(* word *)
global
oseq
Utf8
Relation_Operators
sem_type
syscall syscall_sem
label
arch_decl.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)

Module RegMap. Section Section.

  Context `{arch : arch_decl }.

  Definition map := (* {ffun reg_t -> wreg}. *)
    FinMap.map (T:= reg_t) wreg.

  Definition set (m : map) (x : reg_t) (y : wreg) : map :=
    FinMap.set m x y.

End Section. End RegMap.

Module RegXMap. Section Section.

  Context `{arch : arch_decl }.

  Definition map := (* {ffun reg_t -> wreg}. *)
    FinMap.map (T:= regx_t) wreg.

  Definition set (m : map) (x : regx_t) (y : wreg) : map :=
    FinMap.set m x y.

End Section. End RegXMap.

(* -------------------------------------------------------------------- *)

Module XRegMap. Section Section.
  Context `{arch : arch_decl}.

  Definition map := (* {ffun xreg_t -> wxreg }. *)
    FinMap.map (T:= xreg_t) wxreg.

  Definition set (m : map) (x : xreg_t) (y : wxreg) : map :=
    FinMap.set m x y.

End Section. End XRegMap.

(* -------------------------------------------------------------------- *)

Module RflagMap. Section Section.
  Context `{arch : arch_decl}.

  Definition map := (* {ffun rflag_t -> rflagv}. *)
    FinMap.map (T:= rflag_t) rflagv.

  Definition set (m : map) (x : rflag_t) (y : rflagv) : map :=
    FinMap.set m x y.

End Section. End RflagMap.

(* -------------------------------------------------------------------- *)
Notation regmap   := RegMap.map.
Notation regxmap  := RegXMap.map.
Notation xregmap  := XRegMap.map.
Notation rflagmap := RflagMap.map.

(* -------------------------------------------------------------------- *)
Section SEM.

Context {syscall_state : Type} {sc_sem : syscall_sem syscall_state} `{asm_d : asm} {call_conv: calling_convention}.

Record asmmem : Type := AsmMem {
  asm_rip  : pointer;
  asm_scs : syscall_state_t;
  asm_mem  : mem;
  asm_reg  : regmap;
  asm_regx : regxmap;
  asm_xreg : xregmap;
  asm_flag : rflagmap;
}.

Record asm_state := AsmState {
  asm_m  :> asmmem;
  asm_f  : funname;
  asm_c  : asm_code;
  asm_ip : nat;
}.

Definition preserved_register (r : asm_typed_reg) (m0 m1 : asmmem) :=
  match r with
  | ARReg r => (asm_reg  m0) r = (asm_reg  m1) r
  | ARegX r => (asm_regx m0) r = (asm_regx m1) r
  | AXReg r => (asm_xreg m0) r = (asm_xreg m1) r
  | ABReg r => (asm_flag m0) r = (asm_flag m1) r
  end.

(* FIXME we need to generalize this *)
Class asm_syscall_sem := {
  eval_syscall : syscall_t -> asmmem -> exec asmmem;
  eval_syscall_spec1 :
    forall o s1 s2,
      eval_syscall o s1 = ok s2 ->
      let vargs := map (fun r => Vword (s1.(asm_reg) r)) (take (size (syscall_sig_s o).(scs_tin)) call_reg_args) in
      let vres  := map (fun r => Vword (s2.(asm_reg) r)) (take (size (syscall_sig_s o).(scs_tout)) call_reg_ret) in
      [/\ exec_syscall_s s1.(asm_scs) s1.(asm_mem) o vargs = ok (s2.(asm_scs), s2.(asm_mem), vres),
          (forall r, r \in callee_saved -> preserved_register r s1 s2) &
          s1.(asm_rip) = s2.(asm_rip)];
  eval_syscall_spec2 :
    forall o s1 vargs scs m vres,
      exec_syscall_s s1.(asm_scs) s1.(asm_mem) o vargs = ok (scs, m, vres) ->
      exists s2, eval_syscall o s1 = ok s2;
}.

Context {asm_scsem : asm_syscall_sem}.

Notation asm_result := (result error asmmem).
Notation asm_result_state := (result error asm_state).

(* -------------------------------------------------------------------- *)
Definition st_get_rflag (s : asmmem) (rf : rflag_t) :=
  if s.(asm_flag) rf is Def b then ok b else undef_error.

(* -------------------------------------------------------------------- *)

Definition eval_cond_mem (s : asmmem) (c : cond_t) :=
  eval_cond s.(asm_reg) (st_get_rflag s) c.

(* -------------------------------------------------------------------- *)
Definition st_write_ip (ip : nat) (s : asm_state) :=
  {| asm_m := s.(asm_m)
   ; asm_f := s.(asm_f)
   ; asm_c := s.(asm_c)
   ; asm_ip  := ip |}.

(* -------------------------------------------------------------------- *)
Definition st_update_next (m:asmmem) (s : asm_state) :=
  {| asm_m  := m
   ; asm_f  := s.(asm_f)
   ; asm_c  := s.(asm_c)
   ; asm_ip := s.(asm_ip).+1 |}.

(* -------------------------------------------------------------------- *)
Definition is_label (lbl: label) (i: asm_i) : bool :=
  match asmi_i i with
  | LABEL _ lbl' => lbl == lbl'
  | _ => false
  end.

(* -------------------------------------------------------------------- *)
Definition find_label (lbl : label) (c : asm_code) :=
  let idx := seq.find (is_label lbl) c in
  if idx < size c then ok idx else type_error.

(* -------------------------------------------------------------------- *)
Definition eval_JMP p dst (s: asm_state) : asm_result_state :=
  let: (fn, lbl) := dst in
  if get_fundef (asm_funcs p) fn is Some fd then
    let body := asm_fd_body fd in
    Let ip := find_label lbl body in
    ok
      {| asm_m  := s.(asm_m)
       ; asm_f  := fn
       ; asm_c  := body
       ; asm_ip := ip.+1 (* Jump to instruction immediately following lbl. *)
      |}
  else type_error.

(* -------------------------------------------------------------------- *)
Definition eval_Jcc lbl ct (s : asm_state) : asm_result_state :=
  Let b := eval_cond_mem s ct in
  if b
  then
    (* Jump to instruction immediately following lbl. *)
    Let ip := find_label lbl s.(asm_c) in ok (st_write_ip ip.+1 s)
  else
    ok (st_write_ip s.(asm_ip).+1 s).

(* -------------------------------------------------------------------- *)
Definition word_of_scale (n:nat) : pointer := wrepr Uptr (two_power_nat n).

(* -------------------------------------------------------------------- *)
Definition decode_reg_addr (s : asmmem) (a : reg_address) : pointer := nosimpl (
  let: disp   := a.(ad_disp) in
  let: base   := odflt 0%R (Option.map (s.(asm_reg)) a.(ad_base)) in
  let: scale  := word_of_scale a.(ad_scale) in
  let: offset := odflt 0%R (Option.map (s.(asm_reg)) a.(ad_offset)) in
  disp + base + scale * offset)%R.

Definition decode_addr (s:asmmem) (a:address) : pointer := 
  match a with
  | Areg ra => decode_reg_addr s ra
  | Arip ofs => (s.(asm_rip) + ofs)%R
  end.

(* -------------------------------------------------------------------- *)

Definition eval_asm_arg k (s: asmmem) (a: asm_arg) (ty: stype) : exec value :=
  match a with
  | Condt c   => Let b := eval_cond_mem s c in ok (Vbool b)
  | Imm sz' w =>
    match ty with
    | sword sz => ok (Vword (sign_extend sz w))  (* FIXME should we use sign of zero *)
    | _        => type_error
    end
  | Reg r     => ok (Vword (s.(asm_reg) r))
  | Regx r    => ok (Vword (s.(asm_regx) r))
  | Addr addr =>
    let a := decode_addr s addr in
    match ty with
    | sword sz =>
      match k with
      | AK_compute => ok (Vword (zero_extend sz a))
      | AK_mem al =>
        Let w := read s.(asm_mem) al a sz in
        ok (Vword w)
      end
    | _        => type_error
    end
  | XReg x     => ok (Vword (s.(asm_xreg) x))
  end.

Definition eval_arg_in_v (s:asmmem) (args:asm_args) (a:arg_desc) (ty:stype) : exec value :=
  match a with
  | ADImplicit (IAreg r)   => ok (Vword (s.(asm_reg) r))
  | ADImplicit (IArflag f) => Let b := st_get_rflag s f in ok (Vbool b)
  | ADExplicit k i or =>
    match onth args i with
    | None => type_error
    | Some a =>
      Let _ := assert (check_oreg or a) ErrType in
      eval_asm_arg k s a ty
    end
  end.

Definition eval_args_in (s:asmmem) (args:asm_args) (ain : seq arg_desc) (tin : seq stype) :=
  mapM2 ErrType (eval_arg_in_v s args) ain tin.

Definition eval_instr_op idesc args (s:asmmem) :=
  Let _   := assert (check_i_args_kinds idesc.(id_args_kinds) args) ErrType in
  Let vs  := eval_args_in s args idesc.(id_in) idesc.(id_tin) in
  Let t   := app_sopn _ idesc.(id_semi) vs in
  ok (list_ltuple t).

(* -------------------------------------------------------------------- *)

Definition o2rflagv (b:option bool) : rflagv :=
  if b is Some b then Def b else Undef.

Definition mem_write_rflag (s : asmmem) (f:rflag_t) (b:option bool) :=
  {| asm_mem  := s.(asm_mem);
     asm_scs  := s.(asm_scs);
     asm_reg  := s.(asm_reg);
     asm_regx := s.(asm_regx);
     asm_rip  := s.(asm_rip); 
     asm_xreg := s.(asm_xreg);
     asm_flag := RflagMap.set s.(asm_flag) f (o2rflagv b);
   |}.

(* -------------------------------------------------------------------- *)
Definition mem_write_mem al (l : pointer) sz (w : word sz) (s : asmmem) :=
  Let m := write s.(asm_mem) al l w in ok
  {| asm_mem  := m;
     asm_scs  := s.(asm_scs);
     asm_reg  := s.(asm_reg);
     asm_regx := s.(asm_regx);
     asm_rip  := s.(asm_rip); 
     asm_xreg := s.(asm_xreg);
     asm_flag := s.(asm_flag);
  |}.

(* -------------------------------------------------------------------- *)

Definition mask_word (f : msb_flag) (sz szr : wsize) (old : word szr) : word szr :=
  let mask := if f is MSB_MERGE then wshl (-1)%R (wsize_bits sz)
              else 0%R in
  wand old mask.

Definition word_extend
   (f:msb_flag) (sz szr : wsize) (old : word szr) (new : word sz) : word szr :=
 wxor (mask_word f sz old) (zero_extend szr new).

(* -------------------------------------------------------------------- *)
Definition mem_write_reg (f: msb_flag) (r: reg_t) sz (w: word sz) (m: asmmem) :=
  {|
    asm_mem  := m.(asm_mem);
    asm_scs  := m.(asm_scs);
    asm_reg  := RegMap.set m.(asm_reg) r (word_extend f (m.(asm_reg) r) w);
    asm_regx := m.(asm_regx);
    asm_rip  := m.(asm_rip); 
    asm_xreg := m.(asm_xreg);
    asm_flag := m.(asm_flag);
  |}.

(* -------------------------------------------------------------------- *)
Definition mem_write_regx (f: msb_flag) (r: regx_t) sz (w: word sz) (m: asmmem) :=
  {|
    asm_mem  := m.(asm_mem);
    asm_scs  := m.(asm_scs);
    asm_reg  := m.(asm_reg);
    asm_regx := RegXMap.set m.(asm_regx) r (word_extend f (m.(asm_regx) r) w);
    asm_rip  := m.(asm_rip); 
    asm_xreg := m.(asm_xreg);
    asm_flag := m.(asm_flag);
  |}.

(* -------------------------------------------------------------------- *)
Definition mem_write_xreg (f: msb_flag) (r: xreg_t) sz (w: word sz) (m: asmmem) :=
  {|
    asm_mem  := m.(asm_mem);
    asm_scs  := m.(asm_scs);
    asm_reg  := m.(asm_reg);
    asm_regx := m.(asm_regx);
    asm_rip  := m.(asm_rip);
    asm_xreg := XRegMap.set m.(asm_xreg) r (word_extend f (m.(asm_xreg) r) w);
    asm_flag := m.(asm_flag);
  |}.

(* -------------------------------------------------------------------- *)
Definition mem_write_word (f:msb_flag) (s:asmmem) (args:asm_args) (ad:arg_desc) (sz:wsize) (w: word sz) : exec asmmem :=
  match ad with
  | ADImplicit (IAreg r)   => ok (mem_write_reg f r w s)
  | ADImplicit (IArflag f) => type_error
  | ADExplicit k i or    =>
    match onth args i with
    | None => type_error
    | Some a =>
      Let _ := assert (check_oreg or a) ErrType in
      match a with
      | Reg r   => ok (mem_write_reg  f r w s)
      | Regx r  => ok (mem_write_regx  f r w s)
      | XReg x  => ok (mem_write_xreg f x w s)
      | Addr addr =>
          if k is AK_mem al
          then mem_write_mem al (decode_addr s addr) w s
          else type_error
      | _       => type_error
      end
    end
  end.

Definition mem_write_bool(s:asmmem) (args:asm_args) (ad:arg_desc) (b:option bool) : exec asmmem :=
  match ad with
  | ADImplicit (IArflag f) => ok (mem_write_rflag s f b)
  | _ => type_error
  end.

Definition mem_write_ty (f:msb_flag) (s:asmmem) (args:asm_args) (ad:arg_desc) (ty:stype) : sem_ot ty -> exec asmmem :=
  match ty return sem_ot ty -> exec asmmem with
  | sword sz => @mem_write_word f s args ad sz
  | sbool    => mem_write_bool s args ad
  | sint     => fun _ => type_error
  | sarr _   => fun _ => type_error
  end.

Definition oof_val (ty: stype) (v:value) : exec (sem_ot ty) :=
  match ty return exec (sem_ot ty) with
  | sbool =>
    match v with
    | Vbool b => ok (Some b)
    | Vundef sbool _ => ok None
    | _ => type_error
    end
  | sword ws => to_word ws v
  | _ => type_error
  end.

Definition mem_write_val (f:msb_flag) (args:asm_args) (aty: arg_desc * stype) (v:value) (s:asmmem) : exec asmmem :=
  Let v := oof_val aty.2 v in
  mem_write_ty f s args aty.1 v.

Definition mem_write_vals 
  (f:msb_flag) (s:asmmem) (args:asm_args) (a: seq arg_desc) (ty: seq stype) (vs:values) :=
  fold2 ErrType (mem_write_val f args) (zip a ty) vs s.

Definition exec_instr_op idesc args (s:asmmem) : exec asmmem :=
  Let vs := eval_instr_op idesc args s in
  mem_write_vals idesc.(id_msb_flag) s args idesc.(id_out) idesc.(id_tout) vs.

Definition eval_op o args m := 
  exec_instr_op (instr_desc_op o) args m.

(* -------------------------------------------------------------------- *)
Definition eval_POP (s: asm_state) : exec (asm_state * wreg) :=
  Let sp := truncate_word Uptr (s.(asm_m).(asm_reg) ad_rsp) in
  Let v := read s.(asm_m).(asm_mem) Aligned sp reg_size in
  let m := mem_write_reg MSB_CLEAR ad_rsp (sp + wrepr Uptr (wsize_size Uptr))%R s.(asm_m) in
  ok ({| asm_m := m ; asm_f := s.(asm_f) ; asm_c := s.(asm_c) ; asm_ip := s.(asm_ip).+1 |}, v).

Definition eval_PUSH (w: wreg) (s: asm_state) : exec asm_state :=
  Let sp := truncate_word Uptr (s.(asm_m).(asm_reg) ad_rsp) in
  Let m := mem_write_mem Aligned (sp - wrepr Uptr (wsize_size Uptr))%R w s.(asm_m) in
  let m := mem_write_reg MSB_CLEAR ad_rsp (sp - wrepr Uptr (wsize_size Uptr))%R m in
  ok {| asm_m := m ; asm_f := s.(asm_f) ; asm_c := s.(asm_c) ; asm_ip := s.(asm_ip).+1 |}.

(* -------------------------------------------------------------------- *)
Section PROG.


Context  (p: asm_prog).

Definition label_in_asm (body: asm_code) : seq label :=
  pmap (λ i, if asmi_i i is LABEL ExternalLabel lbl then Some lbl else None) body.

Definition label_in_asm_prog : seq remote_label :=
  [seq (f.1, lbl) | f <- asm_funcs p, lbl <- label_in_asm (asm_fd_body f.2) ].

#[local]
Notation labels := label_in_asm_prog.

Definition return_address_from (s: asm_state) : option (word Uptr) :=
  if oseq.onth s.(asm_c) s.(asm_ip).+1 is Some {| asmi_i := LABEL ExternalLabel lbl |} then
    encode_label labels (asm_f s, lbl)
  else None.

Definition eval_instr (i : asm_i_r) (s: asm_state) : exec asm_state :=
  match i with
  | ALIGN
  | LABEL _ _    => ok (st_write_ip (asm_ip s).+1 s)
  | STORELABEL dst lbl =>
    if encode_label labels (asm_f s, lbl) is Some p then
      let m := mem_write_reg MSB_MERGE dst p s.(asm_m)in
      ok (st_update_next m s)
    else type_error
  | JMP lbl   => eval_JMP p lbl s
  | JMPI d =>
    Let v := eval_asm_arg (AK_mem Aligned) s d (sword Uptr) >>= to_pointer in
    if decode_label labels v is Some lbl then
      eval_JMP p lbl s
    else type_error
  | Jcc   lbl ct => eval_Jcc lbl ct s
  | JAL d lbl =>
      if return_address_from s is Some ra then
        let s' := st_update_next (mem_write_reg MSB_CLEAR d ra s) s in
        eval_JMP p lbl s'
      else type_error
  | CALL lbl =>
      if return_address_from s is Some ra then
        eval_PUSH ra s >>= eval_JMP p lbl
      else type_error
  | POPPC =>
    Let: (s', dst) := eval_POP s in
    if decode_label labels dst is Some lbl then
      eval_JMP p lbl s'
    else type_error
  | AsmOp o args =>
    Let m := eval_op o args s.(asm_m) in
    ok (st_update_next m s)
  | SysCall o =>
    Let m := eval_syscall o s.(asm_m) in
    ok (st_update_next m s)
  end.

(* -------------------------------------------------------------------- *)
Definition fetch_and_eval (s: asm_state) :=
  if oseq.onth s.(asm_c) s.(asm_ip) is Some i then
    eval_instr i.(asmi_i) s
  else type_error.

Definition asmsem1 (s1 s2: asm_state) : Prop :=
  fetch_and_eval s1 = ok s2.

Definition asmsem : relation asm_state := clos_refl_trans asm_state asmsem1.

(* ---------------------------------------------------------------- *)
Record asmsem_invariant (x y: asmmem) : Prop :=
  { asmsem_invariant_rip: asm_rip x = asm_rip y
  ; asmsem_invariant_stack_stable: stack_stable x.(asm_mem) y.(asm_mem)
  }.

Local Notation "(≡)" := asmsem_invariant.
Local Infix "≡" := asmsem_invariant (at level 40).

#[ local ]
Instance asmsem_invariant_Equiv : Equivalence (≡).
Proof.
  split => //.
  - move => x y [] ? ?; split; by symmetry.
  move => x y z [] ? ? [] ? ?; split.
  - by transitivity (asm_rip y).
  by transitivity (asm_mem y).
Qed.

Lemma eval_JMP_invariant (r: remote_label)  (s s': asm_state) :
  eval_JMP p r s = ok s' →
  s ≡ s'.
Proof.
  case: r => fn l.
  rewrite /eval_JMP.
  by case: get_fundef => // fd; t_xrbindP => _ _ <- /=.
Qed.

Lemma mem_write_reg_invariant f r sz (w: word sz) (s: asmmem) :
  mem_write_reg f r w s ≡ s.
Proof. by []. Qed.

Lemma mem_write_mem_invariant al a sz (w: word sz) (s s': asmmem) :
  mem_write_mem al a w s = ok s' → s ≡ s'.
Proof. by rewrite /mem_write_mem; t_xrbindP => ? /Memory.write_mem_stable ? <-. Qed.

Lemma mem_write_val_invariant f xs d v (s s': asmmem) :
  mem_write_val f xs d v s = ok s' →
  s ≡ s'.
Proof.
  rewrite /mem_write_val /mem_write_ty.
  case: d.2 => //; t_xrbindP => /=.
  - by move => ? _; case: d.1 => // - [] // ? /ok_inj <-.
  move => ? ? _; case: d.1 => [ [] | ] //=.
  - by move => ? /ok_inj <-.
  move => k ? ?; case: onth => //; t_xrbindP => - [] // ? _.
  - by move=> /ok_inj <-.
  - by move=> /ok_inj <-.
  - case: k => // al.
    by exact: mem_write_mem_invariant.
  by move => /ok_inj <-.
Qed.

Lemma mem_write_vals_invariant f xs ys tys zs (s s': asmmem) :
  mem_write_vals f s xs ys tys zs = ok s' →
  s ≡ s'.
Proof.
  rewrite /mem_write_vals.
  elim: {ys tys} (zip ys tys) zs s.
  - by case => // s /ok_inj <-.
  case => d ty m ih [] // z zs s /=; t_xrbindP => s1 /mem_write_val_invariant ? /ih ?.
  by transitivity s1.
Qed.

Lemma eval_instr_invariant (i: asm_i_r) (s s': asm_state) :
  eval_instr i s = ok s' →
  s ≡ s'.
Proof.
  case: i => [ | ? ? | ? ? | ? | ? | ? ? | ? ? | ? | | ? ? | ?] /=.
  1, 2: by move => /ok_inj <-.
  - by case: encode_label => // ? /ok_inj <-.
  - exact: eval_JMP_invariant.
  - t_xrbindP => ????; case: decode_label => // ?; exact: eval_JMP_invariant.
  - rewrite /eval_Jcc; t_xrbindP => - []; t_xrbindP => _.
    + by move => _ _ <- /=.
    by move => <-.
  - case: return_address_from => // ra /eval_JMP_invariant /=.
    by rewrite mem_write_reg_invariant.
  - by case: return_address_from => // ra; rewrite /eval_PUSH; t_xrbindP => ? ? _ ? /mem_write_mem_invariant -> <- /eval_JMP_invariant /=; rewrite mem_write_reg_invariant.
  - rewrite /eval_POP; t_xrbindP => _ ? _ ? _ <-.
    by case: decode_label => // ? /eval_JMP_invariant <-.
  - by rewrite /eval_op /exec_instr_op; t_xrbindP => ? ? ? /mem_write_vals_invariant -> <-.
  t_xrbindP => m hm <-.
  have /= [h1 h2 h3]:= eval_syscall_spec1 hm; split => //.
  by have [] := exec_syscallSs h1.
Qed.

Lemma asmsem1_invariant (s s': asm_state) :
  asmsem1 s s' →
  s ≡ s'.
Proof.
  rewrite /asmsem1 /fetch_and_eval.
  by case: onth => // i /eval_instr_invariant.
Qed.

Lemma asmsem_invariantP (s s': asm_state) :
  asmsem s s' →
  s ≡ s'.
Proof.
  by elim/Operators_Properties.clos_refl_trans_ind_left => {s'} // ? ? _ -> /asmsem1_invariant.
Qed.

End PROG.

(* -------------------------------------------------------------------- *)

Definition asmsem_trans P s2 s1 s3 :
  asmsem P s1 s2 -> asmsem P s2 s3 -> asmsem P s1 s3 :=
  rt_trans _ _ s1 s2 s3.

Variant asmsem_exportcall
  (p : asm_prog)
  (fn : funname)
  (m m' : asmmem)
  : Prop :=
  | Asmsem_exportcall :
    forall (fd : asm_fundef),
      get_fundef (asm_funcs p) fn = Some fd
      -> asm_fd_export fd
      -> check_call_conv fd
      -> let s := {| asm_m := m
                   ; asm_f := fn
                   ; asm_c := asm_fd_body fd
                   ; asm_ip := 0
                  |} in
         let s' := {| asm_m := m'
                    ; asm_f := fn
                    ; asm_c := asm_fd_body fd
                    ; asm_ip := size (asm_fd_body fd)
                   |} in
         asmsem p s s'
      -> (forall r,
           r \in callee_saved
           -> preserved_register r m m')
      -> asmsem_exportcall p fn m m'.

End SEM.
