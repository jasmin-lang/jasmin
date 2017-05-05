(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect.
(* ------- *) Require Import memory low_memory expr sem.
(* ------- *) (* - *) Import Memory.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Definition wordbit (w : word) (i : nat) :=
  I64.and (I64.shr w (I64.repr (Z.of_nat i))) I64.one != I64.zero.

(* -------------------------------------------------------------------- *)
Definition word2bits (w : word) : seq bool :=
  [seq wordbit w i | i <- iota 0 I64.wordsize].

(* -------------------------------------------------------------------- *)
Definition msb (w : word) := (I64.signed w <? 0)%Z.
Definition lsb (w : word) := (I64.and w I64.one) != I64.zero.

(* -------------------------------------------------------------------- *)
Parameter shift_mask : word.

(* ==================================================================== *)
Definition label := positive.

(* -------------------------------------------------------------------- *)
Variant register : Type :=
  | RAX | RCX | RDX | RBX | RSP | RBP | RSI | RDI
  | R8  | R9  | R10 | R11 | R12 | R13 | R14 | R15.

(* -------------------------------------------------------------------- *)
Variant rflag : Type := CF | PF | ZF | SF | OF | DF.

(* -------------------------------------------------------------------- *)
Variant scale : Type := Scale1 | Scale2 | Scale4 | Scale8.

(* -------------------------------------------------------------------- *)
Record address : Type := mkAddress {
  ad_disp   : word;
  ad_base   : option register;
  ad_scale  : option scale;
  ad_offset : option register;
}.

(* -------------------------------------------------------------------- *)
Variant oprd : Type :=
| Imm_op     of word
| Reg_op     of register
| Adr_op     of address.

(* -------------------------------------------------------------------- *)
Variant ireg : Type :=
| Imm_ir of word
| Reg_ir of register.

(* -------------------------------------------------------------------- *)
Variant condt : Type :=
| O_ct                  (* overflow *)
| NO_ct                 (* not overflow *)
| B_ct                  (* below, not above or equal *)
| NB_ct                 (* not below, above or equal *)
| E_ct                  (* equal, zero *)
| NE_ct                 (* not equal, not zero *)
| BE_ct                 (* below or equal, not above *)
| NBE_ct                (* not below or equal, above *)
| S_ct                  (* sign *)
| NS_ct                 (* not sign *)
| P_ct                  (* parity, parity even *)
| NP_ct                 (* not parity, parity odd *)
| L_ct                  (* less than, not greater than or equal to *)
| NL_ct                 (* not less than, greater than or equal to *)
| LE_ct                 (* less than or equal to, not greater than *)
| NLE_ct                (* not less than or equal to, greater than *).

(* -------------------------------------------------------------------- *)
Variant asm : Type :=
| LABEL of positive

  (* Data transfert *)
| MOV    of         oprd & oprd    (* copy *)
| CMOVcc of condt & oprd & oprd    (* conditional copy *)

  (* Arithmetic *)
| ADD    of oprd & oprd            (* add unsigned / signed *)
| SUB    of oprd & oprd            (* sub unsigned / signed *)
| MUL    of oprd                   (* mul unsigned *)
| IMUL   of oprd & option oprd & option nat
                                   (* mul   signed *)
| DIV    of oprd                   (* div unsigned *)
| IDIV   of oprd                   (* div   signed *)

| ADC    of oprd & oprd            (* add with carry *)
| SBB    of oprd & oprd            (* sub with borrow *)

| INC    of oprd                   (* increment *)
| DEC    of oprd                   (* decrement *)

  (* Flag *)
| SETcc  of condt & oprd           (* Set byte on condition *)

  (* Pointer arithmetic *)
| LEA    of oprd & oprd            (* Load Effective Address *)

  (* Comparison *)
| TEST   of oprd & oprd            (* Bit-wise logical and CMP *)
| CMP    of oprd & oprd            (* Signed sub CMP *)

  (* Jumps *)
| JMP    of label                  (* Unconditional jump *)
| Jcc    of label & condt          (* Conditional jump *)

  (* Bitwise logical instruction *)
| AND    of oprd & oprd            (* bit-wise and *)
| OR     of oprd & oprd            (* bit-wise or  *)
| XOR    of oprd & oprd            (* bit-wise xor *)
| NOT    of oprd                   (* bit-wise not *)

  (* Bit scan *)
| BSF    of oprd & oprd            (* forward *)
| BSR    of oprd & oprd            (* reverse *)

  (* Bit shifts *)
| SHL    of oprd & ireg            (* unsigned / left  *)
| SHR    of oprd & ireg            (* unsigned / right *)
| SAL    of oprd & ireg            (*   signed / left  *)
| SAR    of oprd & ireg            (*   signed / right *)
.

(* -------------------------------------------------------------------- *)
Scheme Equality for register.
Scheme Equality for rflag.
Scheme Equality for scale.
Scheme Equality for condt.

Definition reg_eqMixin := comparableClass register_eq_dec.
Canonical reg_eqType := EqType register reg_eqMixin.

Definition rflag_eqMixin := comparableClass rflag_eq_dec.
Canonical rflag_eqType := EqType rflag rflag_eqMixin.

Definition scale_eqMixin := comparableClass scale_eq_dec.
Canonical scale_eqType := EqType scale scale_eqMixin.

Definition condt_eqMixin := comparableClass condt_eq_dec.
Canonical condt_eqType := EqType condt condt_eqMixin.

(* -------------------------------------------------------------------- *)
Module RegMap.
  Definition map := register -> word.

  Definition get (m : map) (x : register) := m x.

  Definition set (m : map) (x : register) (y : word) :=
    fun z => if (z == x) then y else m z.
End RegMap.

(* -------------------------------------------------------------------- *)
Module RflagMap.
  Definition map := rflag -> bool.

  Definition get (m : map) (x : rflag) := m x.

  Definition set (m : map) (x : rflag) (y : bool) :=
    fun z => if (z == x) then y else m z.

  Definition update (m : map) (f : rflag -> option bool) :=
    fun rf => odflt (m rf) (f rf).
End RflagMap.

(* -------------------------------------------------------------------- *)
Notation regmap   := RegMap.map.
Notation rflagmap := RflagMap.map.

Definition regmap0   : regmap   := fun x => I64.repr 0.
Definition rflagmap0 : rflagmap := fun x => false.

(* -------------------------------------------------------------------- *)
Record x86_state := X86State {
  xmem : mem;
  xreg : regmap;
  xrf  : rflagmap;
  xc   : seq asm;
  xip  : nat;
}.

(* -------------------------------------------------------------------- *)
Definition st_write_reg (r : register) (w : word) (s : x86_state) :=
  {| xmem := s.(xmem);
     xreg := RegMap.set s.(xreg) r w;
     xrf  := s.(xrf);
     xc   := s.(xc);
     xip  := s.(xip); |}.

(* -------------------------------------------------------------------- *)
Definition st_set_rflags (rf : rflag) (b : bool) (s : x86_state) :=
  {| xmem := s.(xmem);
     xreg := s.(xreg);
     xrf  := RflagMap.set s.(xrf) rf b;
     xc   := s.(xc);
     xip  := s.(xip); |}.

(* -------------------------------------------------------------------- *)
Definition st_update_rflags f (s : x86_state) :=
  {| xmem := s.(xmem);
     xreg := s.(xreg);
     xrf  := RflagMap.update s.(xrf) f;
     xc   := s.(xc);
     xip  := s.(xip); |}.

(* -------------------------------------------------------------------- *)
Definition st_write_mem (l : word) (w : word) (s : x86_state) :=
  Let m := write_mem s.(xmem) l w in ok
  {| xmem := m;
     xreg := s.(xreg);
     xrf  := s.(xrf);
     xc   := s.(xc);
     xip  := s.(xip); |}.

(* -------------------------------------------------------------------- *)
Definition st_write_ip (ip : nat) (s : x86_state) :=
  {| xmem := s.(xmem);
     xreg := s.(xreg);
     xrf  := s.(xrf);
     xc   := s.(xc);
     xip  := ip; |}. 

(* -------------------------------------------------------------------- *)
Coercion word_of_scale (s : scale) : word :=
  I64.repr match s with
  | Scale1 => 1
  | Scale2 => 2
  | Scale4 => 4
  | Scale8 => 8
  end.

(* -------------------------------------------------------------------- *)
Definition decode_addr (s : x86_state) (a : address) : word := nosimpl (
  let: disp   := a.(ad_disp) in
  let: base   := odflt I64.zero (omap (RegMap.get s.(xreg)) a.(ad_base)) in
  let: scale  := odflt I64.one  (omap word_of_scale a.(ad_scale)) in
  let: offset := odflt I64.zero (omap (RegMap.get s.(xreg)) a.(ad_offset)) in

  I64.add disp (I64.add base (I64.mul scale offset))).

(* -------------------------------------------------------------------- *)
Definition write_oprd (o : oprd) (w : word) (s : x86_state) :=
  match o with
  | Imm_op v => type_error
  | Reg_op r => ok (st_write_reg r w s)
  | Adr_op a => st_write_mem (decode_addr s a) w s
  end.

(* -------------------------------------------------------------------- *)
Definition read_oprd (o : oprd) (s : x86_state) :=
  match o with
  | Imm_op v => ok v
  | Reg_op r => ok (RegMap.get s.(xreg) r)
  | Adr_op a => read_mem s.(xmem) (decode_addr s a)
  end.

(* -------------------------------------------------------------------- *)
Definition read_ireg (ir : ireg) (s : x86_state) :=
  match ir with
  | Imm_ir v => v
  | Reg_ir r => RegMap.get s.(xreg) r
  end.

(* -------------------------------------------------------------------- *)
Definition eval_cond (c : condt) (rm : rflagmap) :=
  let get := RflagMap.get rm in
  match c with
  | O_ct   => get OF
  | NO_ct  => ~~ get OF
  | B_ct   => get CF
  | NB_ct  => ~~ get CF
  | E_ct   => get ZF
  | NE_ct  => ~~ get ZF
  | BE_ct  => get CF || get ZF
  | NBE_ct => ~~ get CF && ~~ get ZF
  | S_ct   => get SF
  | NS_ct  => ~~ get SF
  | P_ct   => get PF
  | NP_ct  => ~~ get PF
  | L_ct   => get SF != get OF
  | NL_ct  => get SF == get OF
  | LE_ct  => get ZF || (get SF != get OF)
  | NLE_ct => get ZF && (get SF == get OF)
  end.

(* -------------------------------------------------------------------- *)
Definition aslabel (a : asm) :=
  if a is LABEL lbl then Some lbl else None.

(* -------------------------------------------------------------------- *)
Definition find_label (lbl : label) (a : seq asm) :=
  let idx := seq.index (Some lbl) [seq aslabel i | i <- a] in
  if idx < size a then ok idx else type_error.

(* -------------------------------------------------------------------- *)
Definition SF_of_word (w : word) :=
  msb w.

(* -------------------------------------------------------------------- *)
Definition PF_of_word (w : word) :=
  lsb w.

(* -------------------------------------------------------------------- *)
Definition ZF_of_word (w : word) :=
  I64.eq w I64.zero.

(* -------------------------------------------------------------------- *)
Definition rflags_of_bwop (w : word) := fun rf =>
  match rf with
  | OF => Some false
  | CF => Some false
  | SF => Some (SF_of_word w)
  | PF => Some (PF_of_word w)
  | ZF => Some (ZF_of_word w)
  | _  => None
  end.

(* -------------------------------------------------------------------- *)
Definition rflags_of_aluop (w : word) (v : Z) := fun rf =>
  match rf with
  | OF => Some (I64.signed   w != v)
  | CF => Some (I64.unsigned w != v)
  | SF => Some (SF_of_word w)
  | PF => Some (PF_of_word w)
  | ZF => Some (ZF_of_word w)
  | _  => None
  end.

(* -------------------------------------------------------------------- *)
Definition rflags_of_aluop_nocf (w : word) (v : Z) := fun rf =>
  match rf with
  | OF => Some (I64.signed   w != v)
  | SF => Some (SF_of_word w)
  | PF => Some (PF_of_word w)
  | ZF => Some (ZF_of_word w)
  | _  => None
  end.

(* -------------------------------------------------------------------- *)
Notation x86_result := (result error x86_state).

Implicit Types (ct : condt) (s : x86_state) (o : oprd) (ir : ireg).
Implicit Types (lbl : label).

(* -------------------------------------------------------------------- *)
Definition eval_MOV o1 o2 s : x86_result :=
  type_error.

(* -------------------------------------------------------------------- *)
Definition eval_CMOVcc ct o1 o2 s : x86_result :=
  if eval_cond ct s.(xrf) then eval_MOV o1 o2 s else ok s.

(* -------------------------------------------------------------------- *)
Definition eval_ADD o1 o2 s : x86_result :=
  Let v1 := read_oprd o1 s in
  Let v2 := read_oprd o2 s in
  let v  := I64.add v1 v2 in
  Let s  := write_oprd o1 v s in
  ok (st_update_rflags (rflags_of_aluop v (v1 + v2)%Z) s).

(* -------------------------------------------------------------------- *)
Definition eval_SUB o1 o2 s : x86_result :=
  Let v1 := read_oprd o1 s in
  Let v2 := read_oprd o2 s in
  let v  := I64.sub v1 v2 in
  Let s  := write_oprd o1 v s in
  ok (st_update_rflags (rflags_of_aluop v (v1 - v2)%Z) s).

(* -------------------------------------------------------------------- *)
Definition eval_MUL o s : x86_result :=
  type_error.

(* -------------------------------------------------------------------- *)
Definition eval_IMUL o1 (o2 : option oprd) (n : option nat) s : x86_result  :=
  type_error.

(* -------------------------------------------------------------------- *)
Definition eval_DIV o s : x86_result :=
  type_error.

(* -------------------------------------------------------------------- *)
Definition eval_IDIV o s : x86_result :=
  type_error.

(* -------------------------------------------------------------------- *)
Definition eval_ADC o1 o2 s : x86_result :=
  Let v1 := read_oprd o1 s in
  Let v2 := read_oprd o2 s in
  let c  := if RflagMap.get s.(xrf) CF then I64.one else I64.zero in
  let v  := I64.add_carry v1 v2 c in
  Let s  := write_oprd o1 v s in
  ok (st_update_rflags (rflags_of_aluop v (v1 + v2 + c)%Z) s).

(* -------------------------------------------------------------------- *)
Definition eval_SBB o1 o2 s : x86_result :=
  Let v1 := read_oprd o1 s in
  Let v2 := read_oprd o2 s in
  let c  := if RflagMap.get s.(xrf) CF then I64.one else I64.zero in
  let v  := I64.sub_borrow v1 v2 c in
  Let s  := write_oprd o1 v s in
  ok (st_update_rflags (rflags_of_aluop v (v1 - (v2 + c))%Z) s).

(* -------------------------------------------------------------------- *)
Definition eval_INC o s : x86_result :=
  Let w := read_oprd o s in
  let v := I64.add w I64.one in
  Let s := write_oprd o v s in
  ok (st_update_rflags (rflags_of_aluop_nocf v (w + 1)%Z) s).

(* -------------------------------------------------------------------- *)
Definition eval_DEC o s : x86_result :=
  Let w := read_oprd o s in
  let v := I64.sub w I64.one in
  Let s := write_oprd o v s in
  ok (st_update_rflags (rflags_of_aluop_nocf v (w - 1)%Z) s).

(* -------------------------------------------------------------------- *)
Definition eval_SETcc ct o s : x86_result :=
  let b := eval_cond ct s.(xrf) in
  write_oprd o (if b then I64.one else I64.zero) s.

(* -------------------------------------------------------------------- *)
Definition eval_LEA o1 o2 s : x86_result :=
  type_error.

(* -------------------------------------------------------------------- *)
Definition eval_TEST o1 o2 s : x86_result :=
  Let v1 := read_oprd o1 s in
  Let v2 := read_oprd o2 s in
  let v  := I64.and v1 v2 in
  ok (st_update_rflags (rflags_of_bwop v) s).

(* -------------------------------------------------------------------- *)
Definition eval_CMP o1 o2 s : x86_result :=
  Let v1 := read_oprd o1 s in
  Let v2 := read_oprd o2 s in
  let v  := I64.sub v1 v2 in
  ok (st_update_rflags (rflags_of_aluop v (v1 - v2)%Z) s).

(* -------------------------------------------------------------------- *)
Definition eval_AND o1 o2 s : x86_result :=
  Let v1 := read_oprd o1 s in
  Let v2 := read_oprd o2 s in
  let v  := I64.and v1 v2 in
  Let s  := write_oprd o1 v s in
  ok (st_update_rflags (rflags_of_bwop v) s).

(* -------------------------------------------------------------------- *)
Definition eval_OR o1 o2 s : x86_result :=
  Let v1 := read_oprd o1 s in
  Let v2 := read_oprd o2 s in
  let v  := I64.or v1 v2 in
  Let s  := write_oprd o1 v s in
  ok (st_update_rflags (rflags_of_bwop v) s).

(* -------------------------------------------------------------------- *)
Definition eval_XOR o1 o2 s : x86_result :=
  Let v1 := read_oprd o1 s in
  Let v2 := read_oprd o2 s in
  let v  := I64.xor v1 v2 in
  Let s  := write_oprd o1 v s in
  ok (st_update_rflags (rflags_of_bwop v) s).

(* -------------------------------------------------------------------- *)
Definition eval_NOT o s : x86_result :=
  Let v := read_oprd o s in write_oprd o v s.

(* -------------------------------------------------------------------- *)
Definition eval_BSF o1 o2 s : x86_result :=
  Let v := read_oprd o2 s in
  let b := word2bits v in
  let i := find (pred1 true) b in
  Let s := write_oprd o1 (I64.repr (Z.of_nat i)) s in
  ok (st_set_rflags ZF (ZF_of_word v) s).

(* -------------------------------------------------------------------- *)
Definition eval_BSR o1 o2 s : x86_result :=
  Let v := read_oprd o2 s in
  let b := word2bits v in
  let i := I64.wordsize.-1 - find (pred1 true) (rev b) in
  Let s := write_oprd o1 (I64.repr (Z.of_nat i)) s in
  ok (st_set_rflags ZF (ZF_of_word v) s).

(* -------------------------------------------------------------------- *)
Definition eval_SHL o ir s : x86_result :=
  Let v := read_oprd o s in
  let i := I64.and (read_ireg ir s) shift_mask in

  if i == I64.zero then ok s else
    let rc := msb (I64.shl v (I64.sub i I64.one)) in
    let r  := I64.shl v i in
    Let s  := write_oprd o r s in
    ok (st_update_rflags (fun rf =>
          match rf with
          | OF => Some false
          | CF => Some rc
          | SF => Some (SF_of_word r)
          | PF => Some (PF_of_word r)
          | ZF => Some (ZF_of_word r)
          | _  => None
          end) s).

(* -------------------------------------------------------------------- *)
Definition eval_SHR o ir s : x86_result :=
  Let v := read_oprd o s in
  let i := I64.and (read_ireg ir s) shift_mask in

  if i == I64.zero then ok s else
    let rc := lsb (I64.shru v (I64.sub i I64.one)) in
    let r  := I64.shru v i in
    Let s  := write_oprd o r s in
    ok (st_update_rflags (fun rf =>
          match rf with
          | OF => Some false
          | CF => Some rc
          | SF => Some (SF_of_word r)
          | PF => Some (PF_of_word r)
          | ZF => Some (ZF_of_word r)
          | _  => None
          end) s).

(* -------------------------------------------------------------------- *)
Definition eval_SAL o ir s : x86_result :=
  eval_SHL o ir s.

(* -------------------------------------------------------------------- *)
Definition eval_SAR o ir s : x86_result :=
  Let v := read_oprd o s in
  let i := I64.and (read_ireg ir s) shift_mask in

  if i == I64.zero then ok s else
    let rc := lsb (I64.shr v (I64.sub i I64.one)) in
    let r  := I64.shr v i in
    Let s  := write_oprd o r s in
    ok (st_update_rflags (fun rf =>
          match rf with
          | OF => Some false
          | CF => Some rc
          | SF => Some (SF_of_word r)
          | PF => Some (PF_of_word r)
          | ZF => Some (ZF_of_word r)
          | _  => None
          end) s).

(* -------------------------------------------------------------------- *)
Definition eval_JMP lbl s : x86_result :=
  Let ip := find_label lbl s.(xc) in ok (st_write_ip ip s).

(* -------------------------------------------------------------------- *)
Definition eval_Jcc lbl ct s : x86_result :=
  if eval_cond ct s.(xrf) then eval_JMP lbl s else ok s.

(* -------------------------------------------------------------------- *)
Definition eval_instr (i : asm) s : x86_result :=
  match i with
  | LABEL  _        => ok s
  | MOV    o1 o2    => eval_MOV o1 o2 s
  | CMOVcc ct o1 o2 => eval_CMOVcc ct o1 o2 s
  | ADD    o1 o2    => eval_ADD o1 o2 s
  | SUB    o1 o2    => eval_SUB o1 o2 s
  | MUL    o        => eval_MUL o s
  | IMUL   o1 o2 n  => eval_IMUL o1 o2 n s
  | DIV    o        => eval_DIV o s
  | IDIV   o        => eval_IDIV o s
  | ADC    o1 o2    => eval_ADC o1 o2 s
  | SBB    o1 o2    => eval_SBB o1 o2 s
  | INC    o        => eval_INC o s
  | DEC    o        => eval_DEC o s
  | SETcc  ct o     => eval_SETcc ct o s
  | LEA    o1 o2    => eval_LEA o1 o2 s
  | TEST   o1 o2    => eval_TEST o1 o2 s
  | CMP    o1 o2    => eval_CMP o1 o2 s
  | JMP    lbl      => eval_JMP lbl s
  | Jcc    lbl ct   => eval_Jcc lbl ct s
  | AND    o1 o2    => eval_ADD o1 o2 s
  | OR     o1 o2    => eval_OR o1 o2 s
  | XOR    o1 o2    => eval_XOR o1 o2 s
  | NOT    o        => eval_NOT o s
  | BSF    o1 o2    => eval_BSF o1 o2 s
  | BSR    o1 o2    => eval_BSR o1 o2 s
  | SHL    o ir     => eval_SHL o ir s
  | SHR    o ir     => eval_SHR o ir s
  | SAL    o ir     => eval_SAL o ir s
  | SAR    o ir     => eval_SAR o ir s
  end.

(* -------------------------------------------------------------------- *)
Definition fetch_and_eval s :=
  if nth None (map some s.(xc)) s.(xip) is Some i then
    eval_instr i (st_write_ip s.(xip).+1 s)
  else type_error.
