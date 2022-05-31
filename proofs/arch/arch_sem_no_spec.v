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
syscall
arch_decl
label
trelation_no_spec
values
leakage
arch_sem.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Section SEM_LEAK.

Context {reg regx xreg rflag cond asm_op} {asm_d : asm reg regx xreg rflag cond asm_op}. 

Notation asm_result_state_leak := (result error (asm_state * leak_asm)).

(* -------------------------------------------------------------------- *)
Definition eval_JMP_leak p lptr dst (s: asm_state) : asm_result_state_leak :=
  let: (fn, lbl) := dst in
  if get_fundef (asm_funcs p) fn is Some fd then
    let body := asm_fd_body fd in
    Let ip := find_label lbl body in
    ok ({| asm_m := s.(asm_m) ; asm_f := fn ; asm_c := body ; asm_ip := ip.+1 |}, Ljump lptr dst)
  else type_error.

(* -------------------------------------------------------------------- *)
Definition eval_Jcc_leak lbl ct (s : asm_state) : asm_result_state_leak :=
  Let b := eval_cond_mem s ct in
  let cpc := s.(asm_ip) in 
  Let ip := if b then find_label lbl s.(asm_c) else ok cpc in
  ok ({| asm_m := s.(asm_m); asm_f := s.(asm_f); asm_c := s.(asm_c); asm_ip := ip.+1 |}, Ljumpc b).

(* -------------------------------------------------------------------- *)
Definition eval_asm_arg_leak k (s: asmmem) (a: asm_arg) (ty: stype) : exec (value * seq pointer) :=
  match a with
  | Condt c   => Let b := eval_cond_mem s c in ok ((Vbool b), [::])
  | Imm sz' w =>
    match ty with
    | sword sz => ok (Vword (sign_extend sz w), [::])  (* FIXME should we use sign of zero *)
    | _        => type_error
    end
  | Reg r     => ok (Vword (s.(asm_reg) r), [::])
  | Regx r    => ok (Vword (s.(asm_regx) r), [::])
  | Addr addr =>
    let a := decode_addr s addr in
    match ty with
    | sword sz =>
      if k is AK_compute then ok (Vword (zero_extend sz a), [::])
      else
        Let w := read s.(asm_mem) a sz in
        ok (Vword w, [::a])
    | _        => type_error
    end
  | XReg x     => ok (Vword (s.(asm_xreg) x), [::])
  end.

Definition eval_arg_in_v_leak (s:asmmem) (args:asm_args) (a:arg_desc) (ty:stype) : exec (value * seq pointer) :=
  match a with
  | ADImplicit (IAreg r)   => ok (Vword (s.(asm_reg) r), [::])
  | ADImplicit (IArflag f) => Let b := st_get_rflag s f in ok (Vbool b, [::])
  | ADExplicit k i or =>
    match onth args i with
    | None => type_error
    | Some a =>
      Let _ := assert (check_oreg or a) ErrType in
      eval_asm_arg_leak k s a ty
    end
  end.

Definition eval_args_in_leak (s:asmmem) (args:asm_args) (ain : seq arg_desc) (tin : seq stype) :=
  Let r := mapM2 ErrType (eval_arg_in_v_leak s args) ain tin in ok (unzip1 r, flatten (unzip2 r)).

Definition eval_instr_op_leak idesc args (s:asmmem) :=
  Let _   := assert (check_i_args_kinds idesc.(id_args_kinds) args) ErrType in
  Let vs  := eval_args_in_leak s args idesc.(id_in) idesc.(id_tin) in
  Let t   := app_sopn _ idesc.(id_semi) vs.1 in
  ok (list_ltuple t, vs.2).

(* -------------------------------------------------------------------- *)
Definition mem_write_word_leak (f:msb_flag) (s:asmmem) (args:asm_args) (ad:arg_desc) (sz:wsize) (w: word sz) : exec (asmmem * seq pointer) :=
  match ad with
  | ADImplicit (IAreg r)   => ok (mem_write_reg f r w s, [::])
  | ADImplicit (IArflag f) => type_error
  | ADExplicit _ i or    =>
    match onth args i with
    | None => type_error
    | Some a =>
      Let _ := assert (check_oreg or a) ErrType in
      match a with
      | Reg r   => ok (mem_write_reg  f r w s, [::])
      | Regx r  => ok (mem_write_regx  f r w s, [::])
      | XReg x  => ok (mem_write_xreg f x w s, [::])
      | Addr addr => let p := decode_addr s addr in 
                     Let m := mem_write_mem p w s in
                     ok (m, [:: p])
      | _       => type_error
      end
    end
  end.

Definition mem_write_bool_leak (s:asmmem) (args:asm_args) (ad:arg_desc) (b:option bool) : exec (asmmem * seq pointer) :=
  match ad with
  | ADImplicit (IArflag f) => ok (mem_write_rflag s f b, [::])
  | _ => type_error
  end.

Definition mem_write_ty_leak (f:msb_flag) (s:asmmem) (args:asm_args) (ad:arg_desc) (ty:stype) : sem_ot ty -> exec (asmmem * seq pointer) :=
  match ty return sem_ot ty -> exec (asmmem * seq pointer) with
  | sword sz => @mem_write_word_leak f s args ad sz
  | sbool    => mem_write_bool_leak s args ad
  | sint     => fun _ => type_error
  | sarr _   => fun _ => type_error
  end.

Definition mem_write_val_leak (f:msb_flag) (args:asm_args) (aty: arg_desc * stype) (v:value) (s:asmmem) : exec (asmmem * seq pointer) :=
  Let v := oof_val aty.2 v in
  mem_write_ty_leak f s args aty.1 v.

Fixpoint mem_write_vals_leak  (f:msb_flag) (s:asmmem) (args:asm_args) (a: seq arg_desc) (ty: seq stype) (vs:values) :=
match a, ty, vs with 
  | [::], [::], [::] => ok(s, [::])
  | a1 :: a, ty1 :: ty, v :: vs => Let m := mem_write_val_leak f args (a1, ty1) v s in 
                                   Let ms := mem_write_vals_leak f m.1 args a ty vs in 
                                   ok(ms.1, m.2 ++ ms.2)
  | _, _, _ => Error ErrType 
end.

Definition exec_instr_op_leak idesc args (s:asmmem) : exec (asmmem * leak_asm) :=
  Let vs := eval_instr_op_leak idesc args s in
  Let ms := mem_write_vals_leak idesc.(id_msb_flag) s args idesc.(id_out) idesc.(id_tout) vs.1 in 
  ok(ms.1, Lop (vs.2 ++ ms.2)).

Definition eval_op_leak o args m := 
  exec_instr_op_leak (instr_desc_op o) args m.

(* -------------------------------------------------------------------- *)
Definition eval_POP_leak (s: asm_state) : exec (asm_state * wreg * seq pointer) :=
  Let sp := truncate_word Uptr (s.(asm_m).(asm_reg) stack_pointer_register) in
  Let v := read s.(asm_m).(asm_mem) sp reg_size in
  let m := mem_write_reg MSB_CLEAR stack_pointer_register (sp + wrepr Uptr (wsize_size Uptr))%R s.(asm_m) in
  ok ({| asm_m := m ; asm_f := s.(asm_f) ; asm_c := s.(asm_c) ; asm_ip := s.(asm_ip).+1 |}, v, 
       [:: (sp + wrepr Uptr (wsize_size Uptr))%R]).

Definition eval_PUSH_leak (w: wreg) (s: asm_state) : exec (asm_state * seq pointer) :=
  Let sp := truncate_word Uptr (s.(asm_m).(asm_reg) stack_pointer_register) in
  Let m := mem_write_mem sp w s.(asm_m) in
  let m := mem_write_reg MSB_CLEAR stack_pointer_register (sp - wrepr Uptr (wsize_size Uptr))%R m in
  ok ({| asm_m := m ; asm_f := s.(asm_f) ; asm_c := s.(asm_c) ; asm_ip := s.(asm_ip).+1 |}, 
      [:: (sp - wrepr Uptr (wsize_size Uptr))%R]).

(* -------------------------------------------------------------------- *)
Section PROG_LEAK.

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

Definition eval_instr_leak (i : asm_i) (s: asm_state) : asm_result_state_leak  :=
  match i with
  | ALIGN => ok (st_write_ip (asm_ip s).+1 s, lempty)
  | LABEL _ => ok (st_write_ip (asm_ip s).+1 s, lempty)
  | STORELABEL dst lbl =>
    if encode_label labels (asm_f s, lbl) is Some p then
      let m := mem_write_reg MSB_MERGE dst p s.(asm_m)in
      ok (st_update_next m s, lempty)
    else type_error
  | JMP lbl => eval_JMP_leak p [::] lbl s
  | JMPI d =>
    Let v :=  eval_asm_arg_leak AK_mem s d (sword Uptr) in
    Let vp := to_pointer v.1 in 
    if decode_label labels vp is Some lbl then
      eval_JMP_leak p v.2 lbl s
    else type_error
  | Jcc lbl ct => eval_Jcc_leak lbl ct s
  | JAL d lbl =>
      if return_address_from s is Some ra then
        let s' := st_update_next (mem_write_reg MSB_CLEAR d ra s) s in
        eval_JMP_leak p [::] lbl s'
      else type_error
  | CALL lbl =>
      if return_address_from s is Some ra then
      Let vp := eval_PUSH_leak ra s in
      eval_JMP_leak p vp.2 lbl vp.1 
      else type_error
  | POPPC =>
    Let: (s', dst, sp) := eval_POP_leak s in
    if decode_label labels dst is Some lbl then
      eval_JMP_leak p sp lbl s'
    else type_error
  | AsmOp o args =>
    Let m := eval_op_leak o args s.(asm_m) in
    ok (st_update_next m.1 s, m.2) 
  | SysCall o => 
    Let m := eval_syscall o s.(asm_m) in
    ok (st_update_next m s, lempty) (* Fix needed *)  
  end.

(* -------------------------------------------------------------------- *)
Definition fetch_and_eval_leak (s: asm_state) :=
  if oseq.onth s.(asm_c) s.(asm_ip) is Some i then
    eval_instr_leak i s
  else type_error.

Definition asmsem1_leak (s1: asm_state) (l: leak_asm) (s2: asm_state) : Prop :=
  fetch_and_eval_leak s1 = ok (s2, l).

Definition asmsem_leak := @trace_closure asm_state leak_asm asmsem1_leak.

(* ---------------------------------------------------------------- *)
(*Record asmsem_invariant (x y: asmmem) : Prop :=
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

Lemma eval_JMP_invariant (r: remote_label)  (s s': asm_state) (n: nat) :
  eval_JMP p r s = ok (s', n) →
  s ≡ s' (*/\ 
  exists fd, get_fundef (asm_funcs p) r.2 = Some fd /\
              exists ip,  find_label r.2 (asm_fd_body fd) = ok ip /\
                          n = ip + 1*).
Proof.
  case: r => fn l.
  rewrite /eval_JMP.
  by case: get_fundef => // fd; t_xrbindP=>n' fl <- /= hn. 
Qed.

Lemma mem_write_val_invariant f xs d v n (s s': asmmem) :
  mem_write_val f xs d v s = ok (s', n) →
  s ≡ s'.
Proof.
  rewrite /mem_write_val /mem_write_ty.
  case: d.2 => //; t_xrbindP => /=.
  - by move => ? _; case: d.1 => // - [] // ? /ok_inj [] <- hn.
  move => ? ? _; case: d.1 => [ [] | ] //=.
  - by move => ? /ok_inj [] <- hn.
  move => _ ? ?; case: onth => //; t_xrbindP => - [] //.
  - by move => ? _ _ /ok_inj [] <- hn.
  - by rewrite /mem_write_mem; t_xrbindP => ? _ _ ? ? /Memory.write_mem_stable ? [] <- <- hn /=.
  by move => ? _ _ /ok_inj [] <- hn.
Qed.

Lemma mem_write_vals_invariant f xs ys tys zs n (s s': asmmem) :
  mem_write_vals f s xs ys tys zs = ok (s', n) →
  s ≡ s'.
Proof.
  rewrite /mem_write_vals. 
  elim: ys tys zs=> //=.
  - by move=> [] [] //= [] <- _. 
  move=> a al /= h [] //= sty stys [] //= a' al'.
  t_xrbindP=> - [ym yl] hm /= - [ym' yl'] hm' /= hs hn. eapply h. eapply hm'.
  elim: xs ys tys zs=> //=.
  elim: {ys tys} (zip ys tys) zs s.
  - by case => // s /ok_inj <-.
  case => d ty m ih [] // z zs s /=; t_xrbindP => s1 /mem_write_val_invariant ? /ih ?.
  by transitivity s1.
Qed.

Lemma eval_instr_invariant (i: asm_i) (s s': asm_state) :
  eval_instr i s = ok s' →
  s ≡ s'.
Proof.
  case: i => [ | ? | ? ? | ? | ? | ? ? | ? ? ] /=.
  1, 2: by move => /ok_inj <-.
  - by case: encode_label => // ? /ok_inj <-.
  - exact: eval_JMP_invariant.
  - t_xrbindP => ????; case: decode_label => // ?; exact: eval_JMP_invariant.
  - rewrite /eval_Jcc; t_xrbindP => - []; t_xrbindP => _.
    + by move => _ _ <- /=.
    by move => <-.
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
Qed.*)

End PROG_LEAK.

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

(*Definition asmsem_trans P s2 s1 s3 l1 l2:
  asmsem P s1 l1 s2 -> asmsem P s2 l2 s3 -> asmsem P s1 (l1++l2) s3 :=
  @tc_trans _ _ _ _ _ _ _ _ _ .*) (*FIXME*)

End SEM_LEAK.
