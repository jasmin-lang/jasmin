From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require oseq.
Require Import ZArith
utils
strings wsize
memory_model
(* word *)
global
oseq
Utf8
Relation_Operators
sem_type
arch_decl
label
values.

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
Notation xregmap  := XRegMap.map.
Notation rflagmap := RflagMap.map.

(* -------------------------------------------------------------------- *)
Section SEM.

Context `{asm_d : asm}.

Record asmmem : Type := AsmMem {
  asm_rip  : pointer;
  asm_mem  : mem;
  asm_reg  : regmap;
  asm_xreg : xregmap;
  asm_flag : rflagmap;
}.

Record asm_state := AsmState {
  asm_m  :> asmmem;
  asm_f  : funname;
  asm_c  : asm_code;
  asm_ip : nat;
}.

Notation asm_result := (result error asmmem).
Notation asm_result_state := (result error asm_state).

(* -------------------------------------------------------------------- *)
Definition st_get_rflag (s : asmmem) (rf : rflag_t) :=
  if s.(asm_flag) rf is Def b then ok b else undef_error.

(* -------------------------------------------------------------------- *)

Definition eval_cond_mem (s : asmmem) (c : cond_t) :=
  eval_cond (st_get_rflag s) c.

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
  match i with
  | LABEL lbl' => lbl == lbl'
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
    ok {| asm_m := s.(asm_m) ; asm_f := fn ; asm_c := body ; asm_ip := ip.+1 |}
  else type_error.

(* -------------------------------------------------------------------- *)
Definition eval_Jcc lbl ct (s : asm_state) : asm_result_state :=
  Let b := eval_cond_mem s ct in
  if b then
    Let ip := find_label lbl s.(asm_c) in ok (st_write_ip ip.+1 s)
  else ok (st_write_ip s.(asm_ip).+1 s).

(* -------------------------------------------------------------------- *)
Definition word_of_scale (n:nat) : pointer := wrepr Uptr (2%Z^n)%R.

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
  | Addr addr =>
    let a := decode_addr s addr in
    match ty with
    | sword sz =>
      if k is AK_compute then ok (Vword (zero_extend sz a))
      else
        Let w := read s.(asm_mem) a sz in
        ok (Vword w)
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
     asm_reg  := s.(asm_reg);
     asm_rip  := s.(asm_rip); 
     asm_xreg := s.(asm_xreg);
     asm_flag := RflagMap.set s.(asm_flag) f (o2rflagv b);
   |}.

(* -------------------------------------------------------------------- *)
Definition mem_write_mem (l : pointer) sz (w : word sz) (s : asmmem) :=
  Let m := write s.(asm_mem) l w in ok
  {| asm_mem  := m;
     asm_reg  := s.(asm_reg);
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
    asm_reg  := RegMap.set m.(asm_reg) r (word_extend f (m.(asm_reg) r) w);
    asm_rip  := m.(asm_rip); 
    asm_xreg := m.(asm_xreg);
    asm_flag := m.(asm_flag);
  |}.

(* -------------------------------------------------------------------- *)
Definition mem_write_xreg (f: msb_flag) (r: xreg_t) sz (w: word sz) (m: asmmem) :=
  {|
    asm_mem  := m.(asm_mem);
    asm_reg  := m.(asm_reg);
    asm_rip  := m.(asm_rip);
    asm_xreg := XRegMap.set m.(asm_xreg) r (word_extend f (m.(asm_xreg) r) w);
    asm_flag := m.(asm_flag);
  |}.

(* -------------------------------------------------------------------- *)

(*Lemma word_extend_reg_id r sz (w: word sz) m :
  (U32 ≤ sz)%CMP →
  word_extend_reg r w m = zero_extend U64 w.
Proof.
rewrite /word_extend_reg /merge_word.
by case: sz w => //= w _; rewrite wand0 wxor0.
Qed.
*)

(* -------------------------------------------------------------------- *)
Definition mem_write_word (f:msb_flag) (s:asmmem) (args:asm_args) (ad:arg_desc) (sz:wsize) (w: word sz) : exec asmmem :=
  match ad with
  | ADImplicit (IAreg r)   => ok (mem_write_reg f r w s)
  | ADImplicit (IArflag f) => type_error
  | ADExplicit _ i or    =>
    match onth args i with
    | None => type_error
    | Some a =>
      Let _ := assert (check_oreg or a) ErrType in
      match a with
      | Reg r   => ok (mem_write_reg  f r w s)
      | XReg x  => ok (mem_write_xreg f x w s)
      | Addr addr => mem_write_mem (decode_addr s addr) w s
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
  Let sp := truncate_word Uptr (s.(asm_m).(asm_reg) stack_pointer_register) in
  Let v := read s.(asm_m).(asm_mem) sp reg_size in
  let m := mem_write_reg MSB_CLEAR stack_pointer_register (sp + wrepr Uptr (wsize_size Uptr))%R s.(asm_m) in
  ok ({| asm_m := m ; asm_f := s.(asm_f) ; asm_c := s.(asm_c) ; asm_ip := s.(asm_ip).+1 |}, v).

Definition eval_PUSH (w: wreg) (s: asm_state) : exec asm_state :=
  Let sp := truncate_word Uptr (s.(asm_m).(asm_reg) stack_pointer_register) in
  Let m := mem_write_mem sp w s.(asm_m) in
  let m := mem_write_reg MSB_CLEAR stack_pointer_register (sp - wrepr Uptr (wsize_size Uptr))%R m in
  ok {| asm_m := m ; asm_f := s.(asm_f) ; asm_c := s.(asm_c) ; asm_ip := s.(asm_ip).+1 |}.

(* -------------------------------------------------------------------- *)
Section PROG.

Context  (p: asm_prog).

Definition label_in_asm (body: asm_code) : seq label :=
  pmap (λ i, if i is LABEL lbl then Some lbl else None) body.

Definition label_in_asm_prog : seq remote_label :=
  [seq (f.1, lbl) | f <- asm_funcs p, lbl <- label_in_asm (asm_fd_body f.2) ].

#[local]
Notation labels := label_in_asm_prog.

Definition return_address_from (s: asm_state) : option (word Uptr) :=
  if oseq.onth s.(asm_c) s.(asm_ip).+1 is Some (LABEL lbl) then
    encode_label labels (asm_f s, lbl)
  else None.

Definition eval_instr (i : asm_i) (s: asm_state) : exec asm_state :=
  match i with
  | ALIGN
  | LABEL _      => ok (st_write_ip (asm_ip s).+1 s)
  | STORELABEL dst lbl =>
    if encode_label labels (asm_f s, lbl) is Some p then
      let m := mem_write_reg MSB_MERGE dst p s.(asm_m)in
      ok (st_update_next m s)
    else type_error
  | JMP lbl   => eval_JMP p lbl s
  | JMPI d =>
    Let v := eval_asm_arg AK_mem s d (sword Uptr) >>= to_pointer in
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
  end.

(* -------------------------------------------------------------------- *)
Definition fetch_and_eval (s: asm_state) :=
  if oseq.onth s.(asm_c) s.(asm_ip) is Some i then
    eval_instr i s
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

Lemma mem_write_mem_invariant a sz (w: word sz) (s s': asmmem) :
  mem_write_mem a w s = ok s' → s ≡ s'.
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
  move => _ ? ?; case: onth => //; t_xrbindP => - [] //.
  - by move => ? _ _ /ok_inj <-.
  - move => ? ? _; exact: mem_write_mem_invariant.
  by move => ? _ _ /ok_inj <-.
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

Lemma eval_instr_invariant (i: asm_i) (s s': asm_state) :
  eval_instr i s = ok s' →
  s ≡ s'.
Proof.
  case: i => [ | ? | ? ? | ? | ? | ? ? | ? ? | ? | | ? ? ] /=.
  1, 2: by move => /ok_inj <-.
  - by case: encode_label => // ? /ok_inj <-.
  - exact: eval_JMP_invariant.
  - t_xrbindP => ????; case: decode_label => // ?; exact: eval_JMP_invariant.
  - rewrite /eval_Jcc; t_xrbindP => - []; t_xrbindP => _.
    + by move => _ _ <- /=.
    by move => <-.
  - case: return_address_from => // ra /eval_JMP_invariant /=.
    by rewrite mem_write_reg_invariant.
  - case: return_address_from => // ra; rewrite /eval_PUSH; t_xrbindP => ? ? _ ? /mem_write_mem_invariant -> <- /eval_JMP_invariant /=.
    by rewrite mem_write_reg_invariant.
  - rewrite /eval_POP; t_xrbindP => _ ? _ ? _ <-.
    by case: decode_label => // ? /eval_JMP_invariant <-.
  by rewrite /eval_op /exec_instr_op; t_xrbindP => ? ? ? /mem_write_vals_invariant -> <-.
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
(* TODO: flags may be preserved *)
(* TODO: restore stack pointer of caller? *)
(*
Variant asmsem_fd (P: xprog) (wrip: pointer) fn st st' : Prop :=
| ASMSem_fd fd mp st2
   `(get_fundef P.(xp_funcs) fn = Some fd)
   `(alloc_stack st.(xmem) fd.(xfd_align) fd.(xfd_stk_size) = ok mp)
    (st1 := mem_write_reg fd.(xfd_nstk) (top_stack mp) 
            {| xmem := mp; 
               xreg := st.(xreg); 
               xrip := wrip; 
               xxreg := st.(xxreg); 
               xrf := rflagmap0 |})
    (c := fd.(xfd_body))
    `(asmsem P {| xm := st1 ; xfn := fn ; xc := c ; xip := 0 |} {| xm := st2; xfn := fn ; xc := c; xip := size c |})
    `(st' = {| xmem := free_stack st2.(xmem) fd.(xfd_stk_size); 
               xreg := st2.(xreg);
               xrip := st2.(xrip);
               xxreg := st2.(xxreg) ; 
               xrf := rflagmap0 |})
    .
*)
Definition asmsem_trans P s2 s1 s3 :
  asmsem P s1 s2 -> asmsem P s2 s3 -> asmsem P s1 s3 :=
  rt_trans _ _ s1 s2 s3.

Definition preserved_register (r : reg_t) (m0 m1 : asmmem) :=
  (asm_reg m0) r = (asm_reg m1) r.

Variant asmsem_exportcall
  (callee_saved : seq reg_t)
  (p : asm_prog)
  (fn : funname)
  (m m' : asmmem)
  : Prop :=
  | Asmsem_exportcall :
    forall (fd : asm_fundef),
      get_fundef (asm_funcs p) fn = Some fd
      -> asm_fd_export fd
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
           r \in (callee_saved : seq ceqT_eqType)
           -> preserved_register r m m')
      -> asmsem_exportcall callee_saved p fn m m'.

End SEM.
