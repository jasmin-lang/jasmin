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
Require Import Setoid Morphisms.
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import ZArith utils strings low_memory word global oseq.
Import Utf8 Relation_Operators.
Import Memory.
Require Import sem_type x86_decl x86_instr_decl sem.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Variant asm : Type :=
| ALIGN
| LABEL of label
| STORELABEL of asm_arg & label (* Store the address of a local label *)
  (* Jumps *)
| JMP    of remote_label (* Direct jump *)
| JMPI of asm_arg (* Indirect jump *)
| Jcc    of label & condt  (* Conditional jump *)
| AsmOp     of asm_op & asm_args.

(* -------------------------------------------------------------------- *)
Record xfundef := XFundef {
 xfd_align : wsize;
 xfd_nstk : register;
 xfd_arg  : asm_args;
 xfd_body : seq asm;
 xfd_res  : asm_args;
 xfd_export: bool;
}.

Record xprog : Type :=
  { xp_globs : seq u8;
    xp_funcs : seq (funname * xfundef) }.

(* -------------------------------------------------------------------- *)
Record x86_mem : Type := X86Mem {
  xmem : mem;
  xreg : regmap;
  xrip : pointer;
  xxreg: xregmap;
  xrf  : rflagmap;
}.

(* -------------------------------------------------------------------- *)
(** Compatibility with ssreflect 1.7. *)
Definition comparableMixin :=
  ltac:( exact: comparableMixin || exact: comparableClass ).

Record x86_state := X86State {
  xm   :> x86_mem;
  xfn : funname;
  xc   : seq asm;
  xip  : nat;
}.

Notation x86_result := (result error x86_mem).
Notation x86_result_state := (result error x86_state).

(* -------------------------------------------------------------------- *)
Definition eval_cond (c : condt) (rm : rflagmap) :=
  let get rf :=
    if rm rf is Def b then ok b else undef_error in

  match c with
  | O_ct   => get OF
  | NO_ct  => Let b := get OF in ok (~~ b)
  | B_ct   => get CF
  | NB_ct  => Let b := get CF in ok (~~ b)
  | E_ct   => get ZF
  | NE_ct  => Let b := get ZF in ok (~~ b)
  | S_ct   => get SF
  | NS_ct  => Let b := get SF in ok (~~ b)
  | P_ct   => get PF
  | NP_ct  => Let b := get PF in ok (~~ b)

  | BE_ct =>
      Let cf := get CF in
      Let zf := get ZF in ok (cf || zf)

  | NBE_ct =>
      Let cf := get CF in
      Let zf := get ZF in ok (~~ cf && ~~ zf)

  | L_ct =>
      Let sf  := get SF in
      Let of_ := get OF in ok (sf != of_)

  | NL_ct =>
      Let sf  := get SF in
      Let of_ := get OF in ok (sf == of_)

  | LE_ct =>
      Let zf  := get ZF in
      Let sf  := get SF in
      Let of_ := get OF in ok (zf || (sf != of_))

  | NLE_ct =>
      Let zf  := get ZF in
      Let sf  := get SF in
      Let of_ := get OF in ok (~~ zf && (sf == of_))
  end.

(* -------------------------------------------------------------------- *)
Definition st_write_ip (ip : nat) (s : x86_state) :=
  {| xm := s.(xm);
     xc   := s.(xc);
     xfn := s.(xfn);
     xip  := ip; |}.

(* -------------------------------------------------------------------- *)
Definition is_label (lbl: label) (i: asm) : bool :=
  match i with
  | LABEL lbl' => lbl == lbl'
  | _ => false
  end.

(* -------------------------------------------------------------------- *)
Definition find_label (lbl : label) (a : seq asm) :=
  let idx := seq.find (is_label lbl) a in
  if idx < size a then ok idx else type_error.

(* -------------------------------------------------------------------- *)
Definition eval_JMP p dst (s: x86_state) : x86_result_state :=
  let: (fn, lbl) := dst in
  if get_fundef (xp_funcs p) fn is Some fd then
    let body := xfd_body fd in
    Let ip := find_label lbl body in
    ok {| xm := s.(xm) ; xfn := fn ; xc := body ; xip := ip.+1 |}
  else type_error.

(* -------------------------------------------------------------------- *)
Definition eval_Jcc lbl ct (s: x86_state) : x86_result_state :=
  Let b := eval_cond ct s.(xrf) in
  if b then
    Let ip := find_label lbl s.(xc) in ok (st_write_ip ip.+1 s)
  else ok (st_write_ip (xip s).+1 s).

(* -------------------------------------------------------------------- *)
Definition st_get_rflag (rf : rflag) (s : x86_mem) :=
  if s.(xrf) rf is Def b then ok b else undef_error.

(* -------------------------------------------------------------------- *)

Definition decode_reg_addr (s : x86_mem) (a : reg_address) : pointer := nosimpl (
  let: disp   := a.(ad_disp) in
  let: base   := odflt 0%R (Option.map (s.(xreg)) a.(ad_base)) in
  let: scale  := word_of_scale a.(ad_scale) in
  let: offset := odflt 0%R (Option.map (s.(xreg)) a.(ad_offset)) in
  disp + base + scale * offset)%R.

Definition decode_addr (s:x86_mem) (a:address) : pointer := 
  match a with
  | Areg ra => decode_reg_addr s ra
  | Arip ofs => (s.(xrip) + ofs)%R
  end.

(* -------------------------------------------------------------------- *)
Definition check_oreg or ai :=
  match or, ai with
  | Some r, Reg r' => r == r'
  | Some _, Imm _ _ => true
  | Some _, _      => false
  | None, _        => true
  end.

Definition eval_asm_arg (s: x86_mem) (a: asm_arg) (ty: stype) : exec value :=
  match a with
  | Condt c   => Let b := eval_cond c s.(xrf) in ok (Vbool b)
  | Imm sz' w =>
    match ty with
    | sword sz => ok (Vword (sign_extend sz w))
    | _        => type_error
    end
  | Reg r     => ok (Vword (s.(xreg) r))
  | Adr adr   =>
    match ty with
    | sword sz => Let w := read s.(xmem) (decode_addr s adr) sz in ok (Vword w)
    | _        => type_error
    end
  | XMM x     => ok (Vword (s.(xxreg) x))
  end.

Definition eval_arg_in_v (s:x86_mem) (args:asm_args) (a:arg_desc) (ty:stype) : exec value :=
  match a with
  | ADImplicit (IAreg r)   => ok (Vword (s.(xreg) r))
  | ADImplicit (IArflag f) => Let b := st_get_rflag f s in ok (Vbool b)
  | ADExplicit i or =>
    match onth args i with
    | None => type_error
    | Some a =>
      Let _ := assert (check_oreg or a) ErrType in
      eval_asm_arg s a ty
    end
  end.

Definition eval_args_in (s:x86_mem) (args:asm_args) (ain : seq arg_desc) (tin : seq stype) :=
  mapM2 ErrType (eval_arg_in_v s args) ain tin.

Definition eval_instr_op idesc args (s:x86_mem) :=
  Let _   := assert (idesc.(id_check) args) ErrType in
  Let vs  := eval_args_in s args idesc.(id_in) idesc.(id_tin) in
  Let t   := app_sopn _ idesc.(id_semi) vs in
  ok (list_ltuple t).

(* -------------------------------------------------------------------- *)

Definition o2rflagv (b:option bool) : RflagMap.rflagv :=
  if b is Some b then Def b else Undef.

Definition mem_write_rflag (s : x86_mem) (f:rflag) (b:option bool) :=
  {| xmem  := s.(xmem);
     xreg  := s.(xreg);
     xrip  := s.(xrip); 
     xxreg := s.(xxreg);
     xrf   := RflagMap.oset s.(xrf) f (o2rflagv b);
   |}.

(* -------------------------------------------------------------------- *)
Definition mem_write_mem (l : pointer) sz (w : word sz) (s : x86_mem) :=
  Let m := write s.(xmem) l w in ok
  {| xmem := m;
     xreg := s.(xreg);
     xrip  := s.(xrip); 
     xxreg := s.(xxreg);
     xrf  := s.(xrf);
  |}.

(* -------------------------------------------------------------------- *)
Definition mem_write_xreg (r: xmm_register) (w: u256) (m: x86_mem) :=
  {|
    xmem := m.(xmem);
    xreg := m.(xreg);
    xrip  := m.(xrip); 
    xxreg := XRegMap.set m.(xxreg) r w;
    xrf  := m.(xrf);
  |}.

Definition update_u256 (f: msb_flag) (old: u256) (sz: wsize) (new: word sz) : u256 :=
  match f with
  | MSB_CLEAR => zero_extend U256 new
  | MSB_MERGE =>
    let m : u256 := wshl (-1)%R (wsize_bits sz) in
    wxor (wand old m) (zero_extend U256 new)
  end.

Definition mem_update_xreg f (r: xmm_register) sz (w: word sz) (m: x86_mem) : x86_mem :=
  let old := xxreg m r in
  let w' := update_u256 f old w in
  mem_write_xreg r w' m.

(* -------------------------------------------------------------------- *)

Definition word_extend_reg (r: register) sz (w: word sz) (m: x86_mem) :=
  merge_word (m.(xreg) r) w.

Lemma word_extend_reg_id r sz (w: word sz) m :
  (U32 ≤ sz)%CMP →
  word_extend_reg r w m = zero_extend U64 w.
Proof.
rewrite /word_extend_reg /merge_word.
by case: sz w => //= w _; rewrite wand0 wxor0.
Qed.

Definition mem_write_reg (r: register) sz (w: word sz) (m: x86_mem) :=
  {|
    xmem := m.(xmem);
    xreg := RegMap.set m.(xreg) r (word_extend_reg r w m);
    xrip  := m.(xrip); 
    xxreg := m.(xxreg);
    xrf  := m.(xrf);
  |}.

Definition mem_write_word (f:msb_flag) (s:x86_mem) (args:asm_args) (ad:arg_desc) (sz:wsize) (w: word sz) : exec x86_mem :=
  match ad with
  | ADImplicit (IAreg r)   => ok (mem_write_reg r w s)
  | ADImplicit (IArflag f) => type_error
  | ADExplicit i or    =>
    match onth args i with
    | None => type_error
    | Some a =>
      Let _ := assert (check_oreg or a) ErrType in
      match a with
      | Reg r     => ok (mem_write_reg r w s)
      | Adr adr   => mem_write_mem (decode_addr s adr) w s
      | XMM x     => ok (mem_update_xreg f x w s)
      | _         => type_error
      end
    end
  end.

Definition mem_write_bool(s:x86_mem) (args:asm_args) (ad:arg_desc) (b:option bool) : exec x86_mem :=
  match ad with
  | ADImplicit (IArflag f) => ok (mem_write_rflag s f b)
  | _ => type_error
  end.

Definition mem_write_ty (f:msb_flag) (s:x86_mem) (args:asm_args) (ad:arg_desc) (ty:stype) : sem_ot ty -> exec x86_mem :=
  match ty return sem_ot ty -> exec x86_mem with
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

Definition mem_write_val (f:msb_flag) (args:asm_args) (aty: arg_desc * stype) (v:value) (s:x86_mem) : exec x86_mem :=
  Let v := oof_val aty.2 v in
  mem_write_ty f s args aty.1 v.

Definition mem_write_vals 
  (f:msb_flag) (s:x86_mem) (args:asm_args) (a: seq arg_desc) (ty: seq stype) (vs:values) :=
  fold2 ErrType (mem_write_val f args) (zip a ty) vs s.

Definition exec_instr_op idesc args (s:x86_mem) : exec x86_mem :=
  Let vs := eval_instr_op idesc args s in
  mem_write_vals idesc.(id_msb_flag) s args idesc.(id_out) idesc.(id_tout) vs.

(* -------------------------------------------------------------------- *)
Definition is_special o :=
  match o with
  | LEA _ => true
  | _     => false
  end.

Definition eval_special o args m :=
  match o, args with
  | LEA sz, [:: Reg r; Adr addr] =>
    Let _ := check_size_16_64 sz in
    let p := decode_addr m addr in
    ok (mem_write_reg r (zero_extend sz p) m)
  | _, _ => type_error
  end.

Definition eval_op o args m := 
  if is_special o then
    eval_special o args m
  else
    let id := instr_desc o in
    exec_instr_op id args m.

Section PROG.

Context  (p: xprog).

Definition label_in_asm (body: seq asm) : seq label :=
  pmap (λ i, if i is LABEL lbl then Some lbl else None) body.

Definition label_in_xprog : seq remote_label :=
  [seq (f.1, lbl) | f <- xp_funcs p, lbl <- label_in_asm (xfd_body f.2) ].

Let labels := label_in_xprog.

Definition eval_instr (i : asm) (s: x86_state) : exec x86_state :=
  match i with
  | ALIGN
  | LABEL _      => ok (st_write_ip (xip s).+1 s)
  | STORELABEL dst lbl =>
    if encode_label labels (xfn s, lbl) is Some p then
      Let m := eval_op (MOV Uptr) [:: dst ; Imm p ] s.(xm) in
      ok {| xm := m ; xfn := s.(xfn) ; xc := s.(xc) ; xip := s.(xip).+1 |}
    else type_error
  | JMP lbl   => eval_JMP p lbl s
  | JMPI d =>
    Let v := eval_asm_arg s d (sword Uptr) >>= to_pointer in
    if decode_label labels v is Some lbl then
      eval_JMP p lbl s
    else type_error
  | Jcc   lbl ct => eval_Jcc lbl ct s
  | AsmOp o args =>
    Let m := eval_op o args s.(xm) in
    ok {|
      xm := m;
      xfn := s.(xfn);
      xc := s.(xc);
      xip := s.(xip).+1
    |}
  end.

(* -------------------------------------------------------------------- *)
Definition fetch_and_eval (s: x86_state) :=
  if oseq.onth s.(xc) s.(xip) is Some i then
    eval_instr i s
  else type_error.

Definition x86sem1 (s1 s2: x86_state) : Prop :=
  fetch_and_eval s1 = ok s2.

Definition x86sem : relation x86_state := clos_refl_trans x86_state x86sem1.

End PROG.

(* -------------------------------------------------------------------- *)
(* TODO: flags may be preserved *)
(* TODO: restore stack pointer of caller? *)
(*
Variant x86sem_fd (P: xprog) (wrip: pointer) fn st st' : Prop :=
| X86Sem_fd fd mp st2
   `(get_fundef P.(xp_funcs) fn = Some fd)
   `(alloc_stack st.(xmem) fd.(xfd_align) fd.(xfd_stk_size) = ok mp)
    (st1 := mem_write_reg fd.(xfd_nstk) (top_stack mp) 
            {| xmem := mp; 
               xreg := st.(xreg); 
               xrip := wrip; 
               xxreg := st.(xxreg); 
               xrf := rflagmap0 |})
    (c := fd.(xfd_body))
    `(x86sem P {| xm := st1 ; xfn := fn ; xc := c ; xip := 0 |} {| xm := st2; xfn := fn ; xc := c; xip := size c |})
    `(st' = {| xmem := free_stack st2.(xmem) fd.(xfd_stk_size); 
               xreg := st2.(xreg);
               xrip := st2.(xrip);
               xxreg := st2.(xxreg) ; 
               xrf := rflagmap0 |})
    .
*)
Definition x86sem_trans P s2 s1 s3 :
  x86sem P s1 s2 -> x86sem P s2 s3 -> x86sem P s1 s3 :=
  rt_trans _ _ s1 s2 s3.


