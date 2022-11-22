From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.word Require Import ssrZ.
Require oseq.
Require Import ZArith utils strings low_memory word sem_type global oseq.
Import Utf8 Relation_Operators.
Import Memory.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import x86_decl leakage.

(* -------------------------------------------------------------------- *)
Variant asm_op : Type :=
  (* Data transfert *)
| MOV    of wsize              (* copy *)
| MOVSX  of wsize & wsize      (* sign-extend *)
| MOVZX  of wsize & wsize      (* zero-extend *)
| CMOVcc of wsize              (* conditional copy *)

  (* Arithmetic *)
| ADD    of wsize                  (* add unsigned / signed *)
| SUB    of wsize                  (* sub unsigned / signed *)
| MUL    of wsize                  (* mul unsigned *)
| IMUL   of wsize                             (* mul signed with truncation *)
| IMULr  of wsize   (* oprd * oprd *)         (* mul signed with truncation *)
| IMULri of wsize   (* oprd * oprd * imm *)   (* mul signed with truncation *)

| DIV    of wsize                        (* div unsigned *)
| IDIV   of wsize                        (* div   signed *)
| CQO    of wsize                               (* CWD CDQ CQO: allows sign extention in many words *)
| ADC    of wsize                 (* add with carry *)
| SBB    of wsize                 (* sub with borrow *)

| NEG	   of wsize 	                      (* negation *)

| INC    of wsize                         (* increment *)
| DEC    of wsize                         (* decrement *)

| LZCNT  of wsize             (* number of leading zero *)
  (* Flag *)
| SETcc                           (* Set byte on condition *)
| BT     of wsize                  (* Bit test, sets result to CF *)
| CLC                          (* Clear CF *)
| STC                          (* Set CF *)

  (* Pointer arithmetic *)
| LEA    of wsize              (* Load Effective Address *)

  (* Comparison *)
| TEST   of wsize                  (* Bit-wise logical and CMP *)
| CMP    of wsize                  (* Signed sub CMP *)


  (* Bitwise logical instruction *)
| AND    of wsize  (* bit-wise and *)
| ANDN   of wsize  (* bit-wise andn *)
| OR     of wsize  (* bit-wise or  *)
| XOR    of wsize  (* bit-wise xor *)
| NOT    of wsize  (* bit-wise not *)

  (* Bit shifts *)
| ROR    of wsize    (* rotation / right *)
| ROL    of wsize    (* rotation / left  *)
| RCR    of wsize    (* rotation / right with carry *)
| RCL    of wsize    (* rotation / left  with carry *)
| SHL    of wsize    (* unsigned / left  *)
| SHR    of wsize    (* unsigned / right *)
| SAL    of wsize    (*   signed / left; synonym of SHL *)
| SAR    of wsize    (*   signed / right *)
| SHLD   of wsize    (* unsigned (double) / left *)
| SHRD   of wsize    (* unsigned (double) / right *)
| MULX    of wsize  (* mul unsigned, doesn't affect arithmetic flags *)
| ADCX    of wsize  (* add with carry flag, only writes carry flag *)
| ADOX    of wsize  (* add with overflow flag, only writes overflow flag *)

| BSWAP  of wsize                     (* byte swap *)
| POPCNT of wsize    (* Count bits set to 1 *)

| PEXT   of wsize    (* parallel bits extract *)

  (* SSE instructions *)
| MOVD     of wsize
| VMOV     of wsize 
| VMOVDQU  `(wsize)
| VPMOVSX of velem & wsize & velem & wsize (* parallel sign-extension: sizes are source, source, target, target *)
| VPMOVZX of velem & wsize & velem & wsize (* parallel zero-extension: sizes are source, source, target, target *)
| VPAND    `(wsize)
| VPANDN   `(wsize)
| VPOR     `(wsize)
| VPXOR    `(wsize)
| VPADD    `(velem) `(wsize)
| VPSUB    `(velem) `(wsize)
| VPMULL   `(velem) `(wsize)
| VPMULH   `(velem) `(wsize)   (* signed multiplication of 16-bits*)
| VPMULHU  `(velem) `(wsize)
| VPMULHRS of velem & wsize (* Packed Multiply High with Round and Scale *)
| VPMULU   `(wsize)
| VPEXTR   `(wsize)
| VPINSR   `(velem)
| VPSLL    `(velem) `(wsize)
| VPSRL    `(velem) `(wsize)
| VPSRA    `(velem) `(wsize)
| VPSLLV   `(velem) `(wsize)
| VPSRLV   `(velem) `(wsize)
| VPSLLDQ  `(wsize)
| VPSRLDQ  `(wsize)
| VPSHUFB  `(wsize)
| VPSHUFD  `(wsize)
| VPSHUFHW `(wsize)
| VPSHUFLW `(wsize)
| VSHUFPS  `(wsize)
| VPBLENDD `(wsize)
| VPBROADCAST of velem & wsize
| VMOVSHDUP of velem & wsize (* Replicate 32-bit (“single”) high values *)
| VMOVSLDUP of velem & wsize (* Replicate 32-bit (“single”) low values *)
| VPALIGNR  `(wsize)
| VBROADCASTI128
| VPUNPCKH `(velem) `(wsize)
| VPUNPCKL `(velem) `(wsize)
| VEXTRACTI128
| VINSERTI128
| VPERM2I128
| VPERMD
| VPERMQ
| VPMOVMSKB of wsize & wsize (* source size (U128/256) & dest. size (U32/64) *)
| VPCMPEQ of velem & wsize
| VPCMPGT of velem & wsize
| VPMADDUBSW of wsize
| VPMADDWD of wsize
| VMOVLPD   (* Store low 64-bits from XMM register *)
| VMOVHPD   (* Store high 64-bits from XMM register *)

(* Monitoring *)
| RDTSC   of wsize
| RDTSCP  of wsize

(* AES instructions *)
| AESDEC
| VAESDEC
| AESDECLAST
| VAESDECLAST
| AESENC
| VAESENC
| AESENCLAST
| VAESENCLAST
| AESIMC
| VAESIMC
| AESKEYGENASSIST
| VAESKEYGENASSIST 
.

(* ----------------------------------------------------------------------------- *)
Definition b_ty             := [:: sbool].
Definition b4_ty            := [:: sbool; sbool; sbool; sbool].
Definition b5_ty            := [:: sbool; sbool; sbool; sbool; sbool].

Definition bw_ty    sz      := [:: sbool; sword sz].
Definition bw2_ty   sz      := [:: sbool; sword sz; sword sz].
Definition b2w_ty   sz      := [:: sbool; sbool; sword sz].
Definition b4w_ty   sz      := [:: sbool; sbool; sbool; sbool; sword sz].
Definition b5w_ty   sz      := [:: sbool; sbool; sbool; sbool; sbool; sword sz].
Definition b5w2_ty  sz      := [:: sbool; sbool; sbool; sbool; sbool; sword sz; sword sz].

Definition w_ty     sz      := [:: sword sz].
Definition w2_ty    sz sz'  := [:: sword sz; sword sz'].
Definition w3_ty    sz      := [:: sword sz; sword sz; sword sz].
Definition w4_ty    sz      := [:: sword sz; sword sz; sword sz; sword sz].
Definition w8_ty            := [:: sword8].
Definition w32_ty           := [:: sword32].
Definition w64_ty           := [:: sword64].
Definition w128_ty          := [:: sword128].
Definition w256_ty          := [:: sword256].

Definition w2b_ty   sz sz'  := [:: sword sz; sword sz'; sbool].
Definition ww8_ty   sz      := [:: sword sz; sword8].
Definition ww8b_ty   sz     := [:: sword sz; sword8; sbool].
Definition w2w8_ty   sz     := [:: sword sz; sword sz; sword8].
Definition w128w8_ty        := [:: sword128; sword8].
Definition w128ww8_ty sz    := [:: sword128; sword sz; sword8].
Definition w256w8_ty        := [:: sword256; sword8].
Definition w256w128w8_ty    := [:: sword256; sword128; sword8].
Definition w256x2w8_ty      := [:: sword256; sword256; sword8].

(* ----------------------------------------------------------------------------- *)

Definition SF_of_word sz (w : word sz) :=
  msb w.

Definition PF_of_word sz (w : word sz) : bool :=
  foldl xorb true [seq wbit_n w i | i <- iota 0 8].

Definition ZF_of_word sz (w : word sz) :=
  w == 0%R.

(* -------------------------------------------------------------------- *)
  (*  OF; CF; SF;    PF;    ZF  *)
Definition rflags_of_bwop sz (w : word sz) : (sem_tuple b5_ty) :=
  (*  OF;  CF;    SF;           PF;           ZF  *)
  (:: Some false, Some false, Some (SF_of_word w), Some (PF_of_word w) & Some (ZF_of_word w)).

(* -------------------------------------------------------------------- *)
(*  OF; CF ;SF; PF; ZF  *)
Definition rflags_of_aluop sz (w : word sz) (vu vs : Z) : (sem_tuple b5_ty) :=
  (*  OF;             CF;                SF;           PF;           ZF  *)
  (:: Some (wsigned  w != vs), Some (wunsigned w != vu), Some (SF_of_word w), Some (PF_of_word w) & Some (ZF_of_word w )).

(* -------------------------------------------------------------------- *)
Definition rflags_of_mul (ov : bool) : (sem_tuple b5_ty) :=
  (*  OF; CF; SF;    PF;    ZF  *)
  (:: Some ov, Some ov, None, None & None).

(* -------------------------------------------------------------------- *)

Definition rflags_of_div : (sem_tuple b5_ty):=
  (*  OF;    CF;    SF;    PF;    ZF  *)
  (:: None, None, None, None & None).

(* -------------------------------------------------------------------- *)

Definition rflags_of_andn sz (w: word sz) : (sem_tuple b5_ty) :=
  (* OF ; CF ; SF ; PF ; ZF *)
  (:: Some false , Some false , Some (SF_of_word w) , None & Some (ZF_of_word w) ).

(* -------------------------------------------------------------------- *)

Definition rflags_None_w {sz} w : (sem_tuple (b5w_ty sz)):=
  (*  OF;    CF;    SF;    PF;    ZF  *)
  (:: None, None, None, None, None & w).


(* -------------------------------------------------------------------- *)
(*  OF; SF; PF; ZF  *)
Definition rflags_of_aluop_nocf sz (w : word sz) (vs : Z) : (sem_tuple b4_ty) :=
  (*  OF                 SF          ; PF          ; ZF          ] *)
  (:: Some (wsigned   w != vs), Some (SF_of_word w), Some (PF_of_word w) & Some (ZF_of_word w)).

Definition flags_w {l1} (bs: ltuple l1) {sz} (w: word sz):=
  (merge_tuple bs (w : sem_tuple (w_ty sz))).

Definition flags_w2 {l1} (bs: ltuple l1) {sz} w :=
  (merge_tuple bs (w : sem_tuple (w2_ty sz sz))).

Definition rflags_of_aluop_w sz (w : word sz) (vu vs : Z) :=
  flags_w (rflags_of_aluop w vu vs) w.

Definition rflags_of_aluop_nocf_w sz (w : word sz) (vs : Z) :=
  flags_w (rflags_of_aluop_nocf w vs) w.

Definition rflags_of_bwop_w sz (w : word sz) :=
  flags_w (rflags_of_bwop w) w.

(* -------------------------------------------------------------------- *)

Notation "'ex_tpl' A" := (exec (sem_tuple A)) (at level 200, only parsing).

Fixpoint op_leak_cst (A: Type) (a: A) (l: seq stype) : sem_prod l A:=
  match l return sem_prod l A with 
    | [::] => a
    | t :: l => fun _ => op_leak_cst a l
  end.

Definition op_leak_ty (l : seq stype) & LeakOp : sem_prod l (exec leak_e) := op_leak_cst (Ok error LEmpty) l.

Definition x86_MOV sz (x: word sz) : exec (word sz) :=
  Let _ := check_size_8_64 sz in
  ok x.

Definition x86_MOVSX szi szo (x: word szi) : ex_tpl (w_ty szo) :=
  Let _ :=
    match szi with
    | U8 => check_size_16_64 szo
    | U16 => check_size_32_64 szo
    | U32 => assert (szo == U64) ErrType
    | _ => type_error
    end in
  ok (sign_extend szo x).

Definition x86_MOVZX szi szo (x: word szi) : ex_tpl (w_ty szo) :=
  Let _ :=
    match szi with
    | U8 => check_size_16_64 szo
    | U16 => check_size_32_64 szo
    | _ => type_error
    end in
  ok (zero_extend szo x).

Definition x86_ADD sz (v1 v2 : word sz) : ex_tpl (b5w_ty sz) :=
  Let _ := check_size_8_64 sz in
  ok (rflags_of_aluop_w
    (v1 + v2)%R
    (wunsigned v1 + wunsigned v2)%Z
    (wsigned   v1 + wsigned   v2)%Z).

Definition x86_SUB sz (v1 v2 : word sz) : ex_tpl (b5w_ty sz) :=
  Let _ := check_size_8_64 sz in
  ok (rflags_of_aluop_w
    (v1 - v2)%R
    (wunsigned v1 - wunsigned v2)%Z
    (wsigned   v1 - wsigned   v2)%Z).

Definition x86_CMOVcc sz (b:bool) (w2 w3: word sz) : ex_tpl (w_ty sz) :=
  Let _ := check_size_16_64 sz in
  if b then (ok w2) else (ok w3).

Definition x86_MUL sz (v1 v2: word sz) : ex_tpl (b5w2_ty sz) :=
  Let _  := check_size_16_64 sz in
  let lo := (v1 * v2)%R in
  let hi := wmulhu v1 v2 in
  let ov := wdwordu hi lo in
  let ov := (ov >? wbase sz - 1)%Z in
  ok (flags_w2 (rflags_of_mul ov) (:: hi & lo)).


Definition x86_IMUL_overflow sz (hi lo: word sz) : bool :=
  let ov := wdwords hi lo in
  (ov <? -wbase sz)%Z || (ov >? wbase sz - 1)%Z.

Definition x86_IMUL sz (v1 v2: word sz) : ex_tpl (b5w2_ty sz) :=
  Let _  := check_size_16_64 sz in
  let lo := (v1 * v2)%R in
  let hi := wmulhs v1 v2 in
  let ov := x86_IMUL_overflow hi lo in
  ok (flags_w2 (rflags_of_mul ov) (:: hi & lo)).

Definition x86_IMULt sz (v1 v2: word sz) : ex_tpl (b5w_ty sz) :=
  Let _  := check_size_16_64 sz in
  let lo := (v1 * v2)%R in
  let hi := wmulhs v1 v2 in
  let ov := x86_IMUL_overflow hi lo in
  ok (flags_w (rflags_of_mul ov) lo).

Definition x86_DIV sz (hi lo dv: word sz) : ex_tpl (b5w2_ty sz) :=
  Let _  := check_size_16_64 sz in
  let dd := wdwordu hi lo in
  let dv := wunsigned dv in
  let q  := (dd  /  dv)%Z in
  let r  := (dd mod dv)%Z in
  let ov := (q >? wmax_unsigned sz)%Z in

  if (dv == 0)%Z || ov then type_error else
  ok (flags_w2 (rflags_of_div) (:: (wrepr sz q) & (wrepr sz r))).

Definition x86_IDIV sz (hi lo dv: word sz) : ex_tpl (b5w2_ty sz) :=
  Let _  := check_size_16_64 sz in
  let dd := wdwords hi lo in
  let dv := wsigned dv in
  let q  := (Z.quot dd dv)%Z in
  let r  := (Z.rem  dd dv)%Z in
  let ov := (q <? wmin_signed sz)%Z || (q >? wmax_signed sz)%Z in

  if (dv == 0)%Z || ov then type_error else
  ok (flags_w2 (rflags_of_div) (:: (wrepr sz q) & (wrepr sz r))).

Definition x86_CQO sz (w:word sz) : exec (word sz) :=
  Let _ := check_size_16_64 sz in
  let r : word sz := (if msb w then -1 else 0)%R in
  ok r.

Definition add_carry sz (x y c: Z) : word sz :=
  wrepr sz (x + y + c).

Definition x86_ADC sz (v1 v2 : word sz) (c: bool) : ex_tpl (b5w_ty sz) :=
  Let _  := check_size_8_64 sz in
  let c := Z.b2z c in
  ok (rflags_of_aluop_w
    (add_carry sz (wunsigned v1) (wunsigned v2) c)
    (wunsigned v1 + wunsigned v2 + c)%Z
    (wsigned   v1 + wsigned   v2 + c)%Z).

Definition x86_ADCX sz (v1 v2: word sz) (c:bool) : ex_tpl (bw_ty sz) :=
  Let _ :=  check_size_32_64 sz in
  let (c,w) := waddcarry v1 v2 c in
  ok (Some c, w).

Definition x86_MULX sz (v1 v2: word sz) : ex_tpl (w2_ty sz sz) :=
  Let _ := check_size_32_64 sz in
  ok (wumul v1 v2).

Definition sub_borrow sz (x y c: Z) : word sz :=
  wrepr sz (x - y - c).

Definition x86_SBB sz (v1 v2 : word sz) (c:bool) : ex_tpl (b5w_ty sz) :=
  Let _  := check_size_8_64 sz in
  let c := Z.b2z c in
  ok ( rflags_of_aluop_w
    (sub_borrow sz (wunsigned v1) (wunsigned v2) c)
    (wunsigned v1 - (wunsigned v2 + c))%Z
    (wsigned   v1 - (wsigned   v2 + c))%Z).

Definition x86_NEG sz (w: word sz) : ex_tpl (b5w_ty sz) :=
  Let _  := check_size_8_64 sz in
  let vs := (- wsigned w)%Z in
  let v := (- w)%R in
  ok (flags_w
  ((:: Some (wsigned   v != vs), Some ((w != 0)%R), Some (SF_of_word v), Some (PF_of_word v) & Some (ZF_of_word v)) : sem_tuple b5_ty)
  v).

Definition x86_INC sz (w: word sz) : ex_tpl (b4w_ty sz) :=
  Let _  := check_size_8_64 sz in
  ok (rflags_of_aluop_nocf_w
    (w + 1)
    (wsigned w + 1)%Z).

Definition x86_DEC sz (w: word sz) : ex_tpl (b4w_ty sz) :=
  Let _  := check_size_8_64 sz in
  ok (rflags_of_aluop_nocf_w
    (w - 1)
    (wsigned w - 1)%Z).


Fixpoint leading_zero_aux (n: Z) (k : nat) :=
  if (n <? 2^(64 - k))%Z then k 
  else match k with 
  | 0 => 0
  | S k' => leading_zero_aux n k'
  end.
      
Definition leading_zero sz (w: word sz) : word sz := 
  wrepr sz (leading_zero_aux (wunsigned w) sz).

Definition x86_LZCNT sz (w: word sz) : ex_tpl (b5w_ty sz) := 
   Let _ := check_size_16_64 sz in
   let v := leading_zero w in 
   ok (flags_w 
        (*  OF;     CF;                  SF;   PF;    ZF  *)
         ((:: None, Some (ZF_of_word w), None, None & Some (ZF_of_word v)) : sem_tuple b5_ty) v).

Definition x86_SETcc (b:bool) : ex_tpl (w_ty U8) := ok (wrepr U8 (Z.b2z b)).

Definition x86_BT sz (x y: word sz) : ex_tpl (b_ty) :=
  Let _  := check_size_8_64 sz in
  ok (Some (wbit x y)).

(* -------------------------------------------------------------------- *)
Definition x86_CLC : ex_tpl b_ty := ok (Some false).
Definition x86_STC : ex_tpl b_ty := ok (Some true).

(* -------------------------------------------------------------------- *)
Definition x86_LEA sz (addr: word sz) : ex_tpl (w_ty sz) :=
  Let _  := check_size_16_64 sz in
  ok (addr).

Definition x86_TEST sz (x y: word sz) : ex_tpl  b5_ty :=
  Let _  := check_size_8_64 sz in
  ok (rflags_of_bwop (wand x y)).

Definition x86_CMP sz (x y: word sz) : ex_tpl b5_ty :=
  Let _  := check_size_8_64 sz in
  ok
    (rflags_of_aluop (x - y)
       (wunsigned x - wunsigned y)%Z (wsigned x - wsigned y)%Z).

Definition x86_AND sz (v1 v2: word sz) : ex_tpl (b5w_ty sz) :=
  Let _  := check_size_8_64 sz in
  ok (rflags_of_bwop_w (wand v1 v2)).

Definition x86_ANDN sz (v1 v2: word sz) : ex_tpl (b5w_ty sz) :=
  Let _  := check_size_32_64 sz in
  let w := wandn v1 v2 in
  ok (flags_w (rflags_of_andn w) (w)).

Definition x86_OR sz (v1 v2: word sz) : ex_tpl (b5w_ty sz) :=
  Let _  := check_size_8_64 sz in
  ok (rflags_of_bwop_w (wor v1 v2)).

Definition x86_XOR sz (v1 v2: word sz) : ex_tpl (b5w_ty sz) :=
  Let _  := check_size_8_64 sz in
  ok (rflags_of_bwop_w (wxor v1 v2)).

Definition x86_NOT sz (v: word sz)  : ex_tpl (w_ty sz) :=
  Let _  := check_size_8_64 sz in
  ok (wnot v).

Definition x86_ROR sz (v: word sz) (i: u8) : ex_tpl (b2w_ty sz) :=
  Let _  := check_size_8_64 sz in
  let i := wand i (x86_shift_mask sz) in
  if i == 0%R then
    ok (:: None , None & v)
  else
    let r := wror v (wunsigned i) in
    let CF := msb r in
    let OF := if i == 1%R then Some (CF != msb v) else None in
    ok (:: OF , Some CF & r ).

Definition x86_ROL sz (v: word sz) (i: u8) : ex_tpl (b2w_ty sz) :=
  Let _  := check_size_8_64 sz in
  let i := wand i (x86_shift_mask sz) in
  if i == 0%R then
    ok (:: None , None & v)
  else
    let r := wrol v (wunsigned i) in
    let CF := lsb r in
    let OF := if i == 1%R then Some (msb r != CF) else None in
    ok (:: OF, Some CF & r ).

Definition x86_RCL sz (v: word sz) (i: u8) (cf:bool) : ex_tpl (b2w_ty sz) :=
  Let _  := check_size_8_64 sz in
  let i := wand i (x86_shift_mask sz) in
  let im :=
    match sz with
    | U8 => Zmod (wunsigned i) 9
    | U16 => Zmod (wunsigned i) 17
    | _  => wunsigned i
    end in
  let r := mathcomp.word.word.t2w [tuple of cf::mathcomp.word.word.w2t v] in
  let r := mathcomp.word.word.rotl r (Z.to_nat im) in
  let CF := mathcomp.word.word.msb r in
  let r : word sz := mathcomp.word.word.t2w [tuple of behead (mathcomp.word.word.w2t r)] in
  let OF := if i == 1%R then Some (msb r != CF) else None in
  ok (:: OF, Some CF & r ).

Definition x86_RCR sz (v: word sz) (i: u8) (cf:bool) : ex_tpl (b2w_ty sz) :=
  Let _  := check_size_8_64 sz in
  let i := wand i (x86_shift_mask sz) in
  let im :=
    match sz with
    | U8 => Zmod (wunsigned i) 9
    | U16 => Zmod (wunsigned i) 17
    | _  => wunsigned i
    end in
  let OF := if i == 1%R then Some (msb v != cf) else None in
  let r := mathcomp.word.word.t2w [tuple of rcons (mathcomp.word.word.w2t v) cf] in
  let r := mathcomp.word.word.rotr r (Z.to_nat im) in
  let CF := mathcomp.word.word.lsb r in
  let r : word sz := mathcomp.word.word.t2w [tuple of rev (behead (rev (mathcomp.word.word.w2t r)))] in
  ok (:: OF, Some CF & r ).

Definition rflags_OF {s} sz (i:word s) (r:word sz) rc OF : ex_tpl (b5w_ty sz) :=
  let OF := if i == 1%R then Some OF else None in
  let CF := Some rc in
  let SF := Some (SF_of_word r) in
  let PF := Some (PF_of_word r) in
  let ZF := Some (ZF_of_word r) in
  ok (:: OF, CF, SF, PF, ZF & r).

Definition x86_SHL sz (v: word sz) (i: u8) : ex_tpl (b5w_ty sz) :=
  Let _  := check_size_8_64 sz in
  let i := wand i (x86_shift_mask sz) in
  if i == 0%R then
    ok (rflags_None_w v)
  else
    let rc := msb (wshl v (wunsigned i - 1)) in
    let r  := wshl v (wunsigned i) in
    rflags_OF i r rc (msb r (+) rc).

Definition x86_SHLD sz (v1 v2: word sz) (i: u8) : ex_tpl (b5w_ty sz) :=
  Let _  := check_size_16_64 sz in
  let i := wand i (x86_shift_mask sz) in
  if i == 0%R then
    ok (rflags_None_w v1)
  else
    let rc := msb (wshl v1 (wunsigned i - 1)) in
    let r1 := wshl v1 (wunsigned i) in
    let r2 := wshr v2 (wsize_bits sz - (wunsigned i)) in
    let r  := wor r1 r2 in
    rflags_OF i r rc (msb r (+) rc).

Definition x86_SHR sz (v: word sz) (i: u8) : ex_tpl (b5w_ty sz) :=
  Let _  := check_size_8_64 sz in
  let i := wand i (x86_shift_mask sz) in
  if i == 0%R then
    ok (rflags_None_w v)
  else
    let rc := lsb (wshr v (wunsigned i - 1)) in
    let r  := wshr v (wunsigned i) in
    rflags_OF i r rc (msb r).

Definition x86_SHRD sz (v1 v2: word sz) (i: u8) : ex_tpl (b5w_ty sz) :=
  Let _  := check_size_16_64 sz in
  let i := wand i (x86_shift_mask sz) in
  if i == 0%R then
    ok (rflags_None_w v1)
  else
    let rc := lsb (wshr v1 (wunsigned i - 1)) in
    let r1 := wshr v1 (wunsigned i) in
    let r2 := wshl v2 (wsize_bits sz - (wunsigned i)) in
    let r  := wor r1 r2 in
    rflags_OF i r rc (msb r (+) msb v1).

Definition x86_SAR sz (v: word sz) (i: u8) : ex_tpl (b5w_ty sz) :=
  Let _ := check_size_8_64 sz in
  let i := wand i (x86_shift_mask sz) in
  if i == 0%R then
    ok (rflags_None_w v)
  else
    let rc := lsb (wsar v (wunsigned i - 1)) in
    let r  := wsar v (wunsigned i) in
    rflags_OF i r rc false.

(* ---------------------------------------------------------------- *)
Definition x86_BSWAP sz (v: word sz) : ex_tpl (w_ty sz) :=
  Let _ := check_size_32_64 sz in
  ok (wbswap v).

(* ---------------------------------------------------------------- *)
Definition x86_POPCNT sz (v: word sz): ex_tpl (b5w_ty sz) :=
  Let _ := check_size_16_64 sz in
  let r := popcnt  v in
  ok (:: Some false, Some false, Some false, Some false, Some (ZF_of_word v) & r).

(* ---------------------------------------------------------------- *)
Definition x86_PEXT sz (v1 v2: word sz): ex_tpl (w_ty sz) :=
  let _ := check_size_32_64 sz in
  ok (@pextr sz v1 v2).

(* ---------------------------------------------------------------- *)
Definition x86_MOVD sz (v: word sz) : ex_tpl (w_ty U128) :=
  Let _ := check_size_32_64 sz in
  ok (zero_extend U128 v).

(* ---------------------------------------------------------------- *)
(* How many elements of size ve in a vector of size ws *)
Definition vector_size (ve: velem) (ws: wsize) : option Z :=
  let: (q, r) := Z.div_eucl (wsize_size ws) (wsize_size ve) in
  if r == 0 then Some q else None.

Definition same_vector_length ve sz ve' sz' :=
  match vector_size ve sz, vector_size ve' sz' with
  | Some i, Some j => assert (i == j) ErrType
  | _, _ => Error ErrType
  end.

Definition x86_VPMOVSX (ve: velem) (sz: wsize) (ve': velem) (sz': wsize) (w: word sz) : exec (word sz') :=
  Let _ := check_size_128_256 sz' in
  Let _ := same_vector_length ve sz ve' sz' in
  ok (lift1_vec' (@sign_extend ve ve') sz' w).

Definition x86_VPMOVZX (ve: velem) (sz: wsize) (ve': velem) (sz': wsize) (w: word sz) : exec (word sz') :=
  Let _ := check_size_128_256 sz' in
  Let _ := same_vector_length ve sz ve' sz' in
  ok (lift1_vec' (@zero_extend ve ve') sz' w).

(* ---------------------------------------------------------------- *)
Definition x86_VMOVDQU sz (v: word sz) : ex_tpl (w_ty sz) :=
  Let _ := check_size_128_256 sz in ok v.

(* ---------------------------------------------------------------- *)
Definition x86_u128_binop sz (op: _ → _ → word sz) (v1 v2: word sz) : ex_tpl (w_ty sz) :=
  Let _ := check_size_128_256 sz in
  ok (op v1 v2).

Definition x86_VPAND sz := x86_u128_binop (@wand sz).
Definition x86_VPANDN sz := x86_u128_binop (@wandn sz).
Definition x86_VPOR sz := x86_u128_binop (@wor sz).
Definition x86_VPXOR sz := x86_u128_binop (@wxor sz).

(* ---------------------------------------------------------------- *)
Definition x86_VPADD (ve: velem) sz := x86_u128_binop (lift2_vec ve +%R sz).
Definition x86_VPSUB (ve: velem) sz :=
  x86_u128_binop (lift2_vec ve (fun x y => x - y)%R sz).

Definition x86_VPMULL (ve: velem) sz v1 v2 :=
  Let _ := check_size_32_64 ve in
  x86_u128_binop (lift2_vec ve *%R sz) v1 v2.

Definition x86_VPMULU sz := x86_u128_binop (@wpmulu sz).

(* ---------------------------------------------------------------- *)

Definition x86_VPMULH ve sz v1 v2 :=
  Let _ := assert (ve == VE16) ErrType in
  x86_u128_binop (lift2_vec U16 (@wmulhs U16) sz) v1 v2.

Definition x86_VPMULHU ve sz v1 v2 :=
  Let _ := assert (ve == VE16) ErrType in
  x86_u128_binop (lift2_vec U16 (@wmulhu U16) sz) v1 v2.

Definition x86_VPMULHRS ve sz v1 v2 :=
  Let _ := assert (ve == VE16) ErrType in
  x86_u128_binop (lift2_vec U16 (@wmulhrs U16) sz) v1 v2.

(* ---------------------------------------------------------------- *)
Definition x86_VPEXTR (ve: wsize) (v: u128) (i: u8) : ex_tpl (w_ty ve) :=
  (* This instruction is valid for smaller ve, but semantics is unusual,
      hence compiler correctness would not be provable. *)
  Let _ := check_size_32_64 ve in
  ok (nth (0%R: word ve) (split_vec ve v) (Z.to_nat (wunsigned i))).

(* ---------------------------------------------------------------- *)
Definition x86_VPINSR (ve: velem) (v1: u128) (v2: word ve) (i: u8) : ex_tpl (w_ty U128) :=
  ok (wpinsr v1 v2 i).

Arguments x86_VPINSR : clear implicits.

(* ---------------------------------------------------------------- *)
Definition x86_u128_shift sz' sz (op: word sz' → Z → word sz')
  (v: word sz) (c: u8) : ex_tpl (w_ty sz) :=
  Let _ := check_size_16_64 sz' in
  Let _ := check_size_128_256 sz in
  ok (lift1_vec sz' (λ v, op v (wunsigned c)) sz v).

Arguments x86_u128_shift : clear implicits.

Definition x86_VPSLL (ve: velem) sz := x86_u128_shift ve sz (@wshl _).
Definition x86_VPSRL (ve: velem) sz := x86_u128_shift ve sz (@wshr _).
Definition x86_VPSRA (ve: velem) sz := x86_u128_shift ve sz (@wsar _).

(* ---------------------------------------------------------------- *)
Definition x86_u128_shift_variable ve sz op v1 v2 : ex_tpl (w_ty sz) :=
  Let _ := check_size_32_64 ve in
  Let _ := check_size_128_256 sz in
  ok (lift2_vec ve (λ v1 v2, op v1 (wunsigned v2)) sz v1 v2).

Arguments x86_u128_shift_variable : clear implicits.

Definition x86_VPSLLV ve sz := x86_u128_shift_variable ve sz (@wshl _).
Definition x86_VPSRLV ve sz := x86_u128_shift_variable ve sz (@wshr _).

(* ---------------------------------------------------------------- *)
Definition x86_vpsxldq sz op (v1: word sz) (v2: u8) : ex_tpl (w_ty sz) :=
  Let _ := check_size_128_256 sz in
  ok (op v1 v2).

Definition x86_VPSLLDQ sz := x86_vpsxldq (@wpslldq sz).
Definition x86_VPSRLDQ sz := x86_vpsxldq (@wpsrldq sz).

(* ---------------------------------------------------------------- *)
Definition x86_VPSHUFB sz := x86_u128_binop (@wpshufb sz).

(* ---------------------------------------------------------------- *)
Definition x86_vpshuf sz (op: word sz → Z → word sz) (v1: word sz) (v2: u8) : ex_tpl (w_ty sz) :=
  Let _ := check_size_128_256 sz in
  ok (op v1 (wunsigned v2)).

Arguments x86_vpshuf : clear implicits.

Definition x86_VPSHUFHW sz := x86_vpshuf sz (@wpshufhw _).
Definition x86_VPSHUFLW sz := x86_vpshuf sz (@wpshuflw _).
Definition x86_VPSHUFD sz := x86_vpshuf sz (@wpshufd _).

(* ---------------------------------------------------------------- *)

Definition wshufps_128 (o : u8) (s1 s2: u128) :=
  @make_vec U32 U128 [:: wpshufd1 s1 o 0; wpshufd1 s1 o 1; wpshufd1 s2 o 2; wpshufd1 s2 o 3].

Definition x86_VSHUFPS sz s1 s2 o := 
  Let _ := check_size_128_256 sz in
  ok (lift2_vec U128 (wshufps_128 o) sz s1 s2).

(* ---------------------------------------------------------------- *)
Definition x86_VPUNPCKH ve sz := x86_u128_binop (@wpunpckh sz ve).
Definition x86_VPUNPCKL ve sz := x86_u128_binop (@wpunpckl sz ve).

(* ---------------------------------------------------------------- *)
Definition x86_VPBLENDD sz (v1 v2: word sz) (m: u8) : ex_tpl (w_ty sz) :=
  Let _ := check_size_128_256 sz in
  ok (wpblendd v1 v2 m).

(* ---------------------------------------------------------------- *)
Definition x86_VPBROADCAST ve sz (v: word ve) : ex_tpl (w_ty sz) :=
  Let _ := check_size_128_256 sz in
  ok (wpbroadcast sz v).

(* ---------------------------------------------------------------- *)
Definition x86_VMOVSHDUP ve sz (v: word sz) : ex_tpl (w_ty sz) :=
  Let _ := check_size_128_256 sz in
  Let _ := assert (ve == VE32) ErrType in
  ok (wdup_hi ve v).

Definition x86_VMOVSLDUP ve sz (v: word sz) : ex_tpl (w_ty sz) :=
  Let _ := check_size_128_256 sz in
  Let _ := assert (ve == VE32) ErrType in
  ok (wdup_lo ve v).

(* ---------------------------------------------------------------- *)
Definition x86_VEXTRACTI128 (v: u256) (i: u8) : ex_tpl (w_ty U128) :=
  let r := if lsb i then wshr v U128 else v in
  ok (zero_extend U128 r).

Definition x86_VINSERTI128 (v1: u256) (v2: u128) (m: u8) : ex_tpl (w_ty U256) :=
  ok (winserti128 v1 v2 m).

(* ---------------------------------------------------------------- *)
Definition x86_VPERM2I128 (v1 v2: u256) (m: u8) : ex_tpl (w_ty U256) :=
  ok (wperm2i128 v1 v2 m).

Definition x86_VPERMD (v1 v2: u256): ex_tpl w256_ty :=
  ok (wpermd v1 v2).

Definition x86_VPERMQ (v: u256) (m: u8) : ex_tpl (w_ty U256) :=
  ok (wpermq v m).

(* ---------------------------------------------------------------- *)
Definition x86_VPALIGNR128 (m:u8) (v1 v2: word U128) : word U128 := 
  let v := make_vec U256 [::v2;v1] in
  let v' := wshr v (wunsigned m * 8) in
  @nth (word U128) 0%R (split_vec U128 v') 0.
 
Definition x86_VPALIGNR sz (v1 v2: word sz) (m:u8) : ex_tpl (w_ty sz) := 
  Let _ := check_size_128_256 sz in
  ok (lift2_vec U128 (x86_VPALIGNR128 m) sz v1 v2).

(* ---------------------------------------------------------------- *)
Definition x86_VPMOVMSKB ssz dsz (v : word ssz): ex_tpl (w_ty dsz) :=
  Let _ := check_size_32_64 dsz in
  Let _ := check_size_128_256 ssz in
  ok (wpmovmskb dsz v).

(* ---------------------------------------------------------------- *)
Definition x86_VPCMPEQ (ve: velem) sz (v1 v2: word sz): ex_tpl(w_ty sz) :=
  Let _ := check_size_8_64 ve in
  Let _ := check_size_128_256 sz in
  ok (wpcmpeq ve v1 v2).

Definition x86_VPCMPGT (ve: velem) sz (v1 v2: word sz): ex_tpl(w_ty sz) :=
  Let _ := check_size_8_64 ve in
  Let _ := check_size_128_256 sz in
  ok (wpcmpgt ve v1 v2).

(* ---------------------------------------------------------------- *)
Definition x86_VPMADDUBSW sz (v v1: word sz) : ex_tpl (w_ty sz) :=
  Let _ := check_size_128_256 sz in
  ok (wpmaddubsw v v1).

Definition x86_VPMADDWD sz (v v1: word sz) : ex_tpl (w_ty sz) :=
  Let _ := check_size_128_256 sz in
  ok (wpmaddwd v v1).

(* ---------------------------------------------------------------- *)
Definition x86_VMOVLPD (v: u128): ex_tpl (w_ty U64) :=
  ok (zero_extend U64 v).

Definition x86_VMOVHPD (v: u128): ex_tpl (w_ty U64) :=
  ok (zero_extend U64 (wshr v 64)).

(* TODO: move this in word *)
(* FIXME: Extraction fail if they are parameter, more exactly extracted program fail *)
(*
Parameter wAESDEC          : u128 -> u128 -> u128.
Parameter wAESDECLAST      : u128 -> u128 -> u128.
Parameter wAESENC          : u128 -> u128 -> u128.
Parameter wAESENCLAST      : u128 -> u128 -> u128.
Parameter wAESIMC          : u128 -> u128.
Parameter wAESKEYGENASSIST : u128 -> u8 -> u128.

Definition x86_AESDEC          (v1 v2 : u128) : ex_tpl (w_ty U128) := ok (wAESDEC          v1 v2).
Definition x86_AESDECLAST      (v1 v2 : u128) : ex_tpl (w_ty U128) := ok (wAESDECLAST      v1 v2).
Definition x86_AESENC          (v1 v2 : u128) : ex_tpl (w_ty U128) := ok (wAESENC          v1 v2).
Definition x86_AESENCLAST      (v1 v2 : u128) : ex_tpl (w_ty U128) := ok (wAESENCLAST      v1 v2).
Definition x86_AESIMC          (v1    : u128) : ex_tpl (w_ty U128) := ok (wAESIMC          v1).
Definition x86_AESKEYGENASSIST (v1 v2 : u128) : ex_tpl (w_ty U128) := ok (wAESKEYGENASSIST v1 v2).
*)

Definition x86_AESDEC          (v1 v2 : u128) : ex_tpl (w_ty U128) := ok (wrepr U128 0).
Definition x86_AESDECLAST      (v1 v2 : u128) : ex_tpl (w_ty U128) := ok (wrepr U128 0).
Definition x86_AESENC          (v1 v2 : u128) : ex_tpl (w_ty U128) := ok (wrepr U128 0).
Definition x86_AESENCLAST      (v1 v2 : u128) : ex_tpl (w_ty U128) := ok (wrepr U128 0).
Definition x86_AESIMC          (v1    : u128) : ex_tpl (w_ty U128) := ok (wrepr U128 0).
Definition x86_AESKEYGENASSIST (v1 : u128) (v2 : u8) : ex_tpl (w_ty U128) := ok (wrepr U128 0).

(* ----------------------------------------------------------------------------- *)
Coercion F f := ADImplicit (IArflag f).
Coercion R r := ADImplicit (IAreg r).

Definition implicit_flags      := map F [::OF; CF; SF; PF; ZF].
Definition implicit_flags_noCF := map F [::OF; SF; PF; ZF].

Definition iCF := F CF.

(* -------------------------------------------------------------------- *)

Variant prim_constructor :=
  | PrimP of wsize & (wsize -> asm_op)
  | PrimM of asm_op
  | PrimV of (velem -> wsize -> asm_op)
  | PrimX of (wsize -> wsize -> asm_op)
  | PrimVV of (velem → wsize → velem → wsize → asm_op)
  .

Variant arg_kind :=
  | CAcond
  | CAreg
  | CAxmm
  | CAmem of bool (* true if Global is allowed *)
  | CAimm of wsize
  .

Definition arg_kinds := seq arg_kind.
Definition args_kinds := seq arg_kinds.
Definition i_args_kinds := seq args_kinds.

Definition check_arg_kind (a:asm_arg) (cond: arg_kind) :=
  match a, cond with
  | Condt _, CAcond => true
  | Imm sz _, CAimm sz' => sz == sz'
  | Glob _, CAmem b => b
  | Reg _, CAreg => true
  | Adr _, CAmem _ => true
  | XMM _, CAxmm   => true
  | _, _ => false
  end.

Definition check_arg_kinds (a:asm_arg) (cond:arg_kinds) :=
  has (check_arg_kind a) cond.

Definition check_args_kinds (a:asm_args) (cond:args_kinds) :=
 all2 check_arg_kinds a cond.

Definition check_i_args_kinds (cond:i_args_kinds) (a:asm_args) :=
  has (check_args_kinds a) cond.

Notation mk_instr str_jas tin tout ain aout msb semi seml check nargs wsizei max_imm safe_cond pp_asm:=
 {|
  id_msb_flag := msb;
  id_tin      := tin;
  id_in       := ain;
  id_tout     := tout;
  id_out      := aout;
  id_semi     := semi;
  id_seml     := seml;
  id_nargs    := nargs;
  id_check    := (fun a => check_i_args_kinds check a);
  id_eq_size  := refl_equal;
  id_tin_narr := refl_equal;
  id_check_dest := refl_equal;
  id_str_jas  := str_jas;
  id_wsize    := wsizei;
  id_max_imm  := max_imm;
  id_safe     := safe_cond;
  id_pp_asm   := pp_asm;
|}.

Notation mk_instr_pp  name tin tout ain aout msb semi seml check nargs wsizei max_imm prc pp_asm :=
  (mk_instr (pp_s name%string) tin tout ain aout msb semi seml check nargs wsizei max_imm [::] pp_asm,
   (name%string, prc)) (only parsing).

Notation mk_instr_w_w name semi msb ain aout nargs check max_imm prc pp_asm :=
 ((fun sz =>
  mk_instr (pp_sz name sz) (w_ty sz) (w_ty sz) ain aout msb (semi sz) (op_leak_ty (w_ty sz)) (check sz) nargs sz (max_imm sz) [::] (pp_asm sz)), (name%string,prc)) (only parsing).

Notation mk_instr_w_w'_10 name sign semi check max_imm prc pp_asm :=
 ((fun szo szi =>
  mk_instr (pp_sz_sz name sign szo szi) (w_ty szi) (w_ty szo) [:: E 1] [:: E 0] MSB_CLEAR (semi szi szo) (op_leak_ty (w_ty szi)) (check szi szo) 2 szi (max_imm szi) [::] (pp_asm szi szo)), (name%string,prc)) (only parsing).

Notation mk_instr_bw2_w_0211 name semi check max_imm prc pp_asm :=
 ((fun sz =>
  mk_instr (pp_sz name sz) (bw2_ty sz) (w_ty sz) [:: E 0; E 2; E 1] [:: E 1] MSB_CLEAR (semi sz) (op_leak_ty (bw2_ty sz)) (check sz) 3 sz (max_imm sz) [::] (pp_asm sz)), (name%string, prc))  (only parsing).

Notation mk_instr_w_b5w name semi msb ain aout nargs check max_imm prc pp_asm :=
 ((fun sz =>
  mk_instr (pp_sz name sz) (w_ty sz) (b5w_ty sz) ain (implicit_flags ++ aout) msb (semi sz)  (op_leak_ty (w_ty sz)) (check sz) nargs sz (max_imm sz) [::] (pp_asm sz)), (name%string,prc))  (only parsing).

Notation mk_instr_w_b4w_00 name semi check max_imm prc pp_asm := ((fun sz =>
  mk_instr (pp_sz name sz) (w_ty sz) (b4w_ty sz) [:: E 0] (implicit_flags_noCF ++ [:: E 0]) MSB_CLEAR (semi sz) (op_leak_ty (w_ty sz)) (check sz) 1 sz (max_imm sz) [::] (pp_asm sz)), (name%string,prc))  (only parsing).

Notation mk_instr_w2_b name semi msb ain aout nargs check max_imm prc pp_asm := ((fun sz =>
  mk_instr (pp_sz name sz) (w2_ty sz sz) (b_ty) ain aout msb (semi sz) (op_leak_ty (w2_ty sz sz)) (check sz) nargs sz (max_imm sz) [::] (pp_asm sz)), (name%string,prc))  (only parsing).

Notation mk_instr_w2_b5 name semi msb ain nargs check max_imm prc pp_asm := ((fun sz =>
  mk_instr (pp_sz name sz) (w2_ty sz sz) (b5_ty) ain implicit_flags msb (semi sz) (op_leak_ty (w2_ty sz sz)) (check sz) nargs sz (max_imm sz) [::] (pp_asm sz)), (name%string,prc))  (only parsing).

Notation mk_instr_w2_b5w name semi msb ain aout nargs check max_imm prc pp_asm := ((fun sz =>
  mk_instr (pp_sz name sz) (w2_ty sz sz) (b5w_ty sz) ain (implicit_flags ++ aout) msb (semi sz) (op_leak_ty (w2_ty sz sz)) (check sz) nargs sz (max_imm sz) [::] (pp_asm sz)), (name%string,prc))  (only parsing).

Notation mk_instr_w2_b5w_010 name semi check max_imm prc pp_asm := ((fun sz =>
  mk_instr (pp_sz name sz) (w2_ty sz sz) (b5w_ty sz) [:: E 0; E 1] (implicit_flags ++ [:: E 0]) MSB_CLEAR (semi sz) (op_leak_ty (w2_ty sz sz)) (check sz) 2 sz (max_imm sz) [::] (pp_asm sz)), (name%string,prc)) (only parsing).

Notation mk_instr_w2b_b5w_010 name semi check max_imm prc pp_asm := ((fun sz =>
  mk_instr (pp_sz name sz) (w2b_ty sz sz) (b5w_ty sz) ([:: E 0; E 1] ++ [::iCF]) (implicit_flags ++ [:: E 0]) MSB_CLEAR (semi sz) 
  (op_leak_ty (w2b_ty sz sz)) (check sz) 2 sz (max_imm sz) [::] (pp_asm sz)), (name%string,prc))  (only parsing).

Notation mk_instr_w2b_bw name semi flag check max_imm prc pp_asm := ((fun sz =>
  mk_instr (pp_sz name sz) (w2b_ty sz sz) (bw_ty sz) ([:: E 0; E 1] ++ [::F flag]) ([::F flag; E 0]) MSB_CLEAR (semi sz) (op_leak_ty (w2b_ty sz sz)) (check sz) 2 sz (max_imm sz) [::] (pp_asm sz)), (name%string,prc))  (only parsing).

Notation mk_instr_w2_b5w2 name semi msb ain aout nargs check max_imm prc pp_asm := ((fun sz =>
  mk_instr (pp_sz name sz) (w2_ty sz sz) (b5w2_ty sz) ain (implicit_flags ++ aout) msb (semi sz) (op_leak_ty (w2_ty sz sz)) (check sz) nargs sz (max_imm sz) [::] (pp_asm sz)), (name%string,prc))  (only parsing).

Notation mk_instr_w3_b5w2_da0ad name s semi check max_imm prc pp_asm := ((fun sz =>
  mk_instr (pp_sz name sz) (w3_ty sz) (b5w2_ty sz) [:: R RDX; R RAX; E 0]  (implicit_flags ++ [:: R RAX; R RDX]) MSB_CLEAR (semi sz) (λ LO, @div_leak LO s sz)
  (check sz) 1 sz (max_imm sz) [::NotZero sz 2] (pp_asm sz)), (name%string,prc))  (only parsing).

Notation mk_instr_w2_w_120 name semi check max_imm prc pp_asm := ((fun sz =>
  mk_instr (pp_sz name sz) (w2_ty sz sz) (w_ty sz) [:: E 1 ; E 2] [:: E 0] MSB_CLEAR (semi sz)  (op_leak_ty (w2_ty sz sz)) (check sz) 3 sz (max_imm sz) [::] (pp_asm sz)), (name%string,prc))  (only parsing).

Notation mk_instr_w4_w name semi msb ain aout nargs check max_imm prc pp_asm:= ((fun sz =>
  mk_instr (pp_sz name sz) (w4_ty sz) (w_ty sz) ain aout msb (semi sz) (op_leak_ty (w4_ty sz)) check nargs sz (max_imm sz) [::] (pp_asm sz)), (name%string,prc))  (only parsing). 

Notation mk_instr_ww8_w_120 name semi check max_imm prc pp_asm := ((fun sz =>
  mk_instr (pp_sz name sz) (ww8_ty sz) (w_ty sz) [:: E 1 ; E 2] [:: E 0]  MSB_CLEAR (semi sz) (op_leak_ty (ww8_ty sz)) (check sz) 3 sz (max_imm sz) [::] (pp_asm sz)), (name%string,prc))  (only parsing).

Notation mk_instr_ww8_b2w_0c0 name semi check max_imm prc pp_asm := ((fun sz =>
  mk_instr (pp_sz name sz) (ww8_ty sz) (b2w_ty sz) [:: E 0; ADExplicit 1 (Some RCX)] [::F OF; F CF; E 0] MSB_CLEAR (semi sz) (op_leak_ty (ww8_ty sz)) (check sz) 2 sz (max_imm sz) [::] (pp_asm sz)), (name%string,prc))  (only parsing).

Notation mk_instr_ww8b_b2w_0c0 name semi check max_imm prc pp_asm := ((fun sz =>
  mk_instr (pp_sz name sz) (ww8b_ty sz) (b2w_ty sz) [:: E 0; ADExplicit 1 (Some RCX); F CF] [::F OF; F CF; E 0] MSB_CLEAR (semi sz) (op_leak_ty (ww8b_ty sz)) (check sz) 2 sz (max_imm sz) [::] (pp_asm sz)), (name%string,prc))  (only parsing).

Notation mk_instr_ww8_b5w_0c0 name semi check max_imm prc pp_asm := ((fun sz =>
  mk_instr (pp_sz name sz) (ww8_ty sz) (b5w_ty sz) [:: E 0; ADExplicit 1 (Some RCX)] (implicit_flags ++ [:: E 0]) MSB_CLEAR (semi sz) (op_leak_ty (ww8_ty sz)) (check sz) 2 sz (max_imm sz) [::] (pp_asm sz)), (name%string,prc))  (only parsing).

Notation mk_instr_w2w8_b5w_01c0 name semi check max_imm prc pp_asm := ((fun sz =>
  mk_instr (pp_sz name sz) (w2w8_ty sz) (b5w_ty sz) [:: E 0; E 1; ADExplicit 2 (Some RCX)] (implicit_flags ++ [:: E 0]) MSB_CLEAR (semi sz) (op_leak_ty (w2w8_ty sz)) (check sz) 3 sz (max_imm sz) [::] (pp_asm sz)), (name%string,prc))  (only parsing).

Notation mk_instr_w2w8_w_1230 name semi check max_imm prc pp_asm := ((fun sz =>
  mk_instr (pp_sz name sz) (w2w8_ty sz) (w_ty sz) [:: E 1 ; E 2 ; E 3] [:: E 0] MSB_CLEAR (semi sz) (op_leak_ty (w2w8_ty sz)) (check sz) 4 sz (max_imm sz) [::] (pp_asm sz)), (name%string,prc))  (only parsing).

Notation mk_instr_w_w128_10 name msb semi check max_imm prc pp_asm := ((fun sz =>
  mk_instr (pp_sz name sz) (w_ty sz) (w128_ty) [:: E 1] [:: E 0] msb (semi sz) (op_leak_ty (w_ty sz)) (check sz) 2 sz (max_imm sz) [::] (pp_asm sz)), (name%string,prc))  (only parsing).

Notation mk_ve_instr_w_w_10 name semi check max_imm prc pp_asm := ((fun (ve:velem) sz =>
  mk_instr (pp_ve_sz name ve sz) (w_ty _) (w_ty sz) [:: E 1] [:: E 0] MSB_CLEAR (semi ve sz) (op_leak_ty (w_ty _)) (check sz) 2 sz (max_imm sz) [::] (pp_asm ve sz)), (name%string,prc))  (only parsing).

Notation mk_ve_instr_w2_w_120 name semi check max_imm prc pp_asm := ((fun (ve:velem) sz =>
  mk_instr (pp_ve_sz name ve sz) (w2_ty sz sz) (w_ty sz) [:: E 1 ; E 2] [:: E 0] MSB_CLEAR (semi ve sz) (op_leak_ty (w2_ty sz sz)) (check sz) 3 sz (max_imm sz) [::] (pp_asm ve sz)), (name%string,prc))  (only parsing).

Notation mk_ve_instr_ww8_w_120 name semi check max_imm prc pp_asm := ((fun ve sz =>
  mk_instr (pp_ve_sz name ve sz) (ww8_ty sz) (w_ty sz) [:: E 1 ; E 2] [:: E 0] MSB_CLEAR (semi ve sz) (op_leak_ty (ww8_ty sz)) (check sz) 3 sz (max_imm sz) [::] (pp_asm ve sz)), (name%string,prc))  (only parsing).

Definition msb_dfl := MSB_CLEAR.

Definition no_imm (sz:wsize) : option wsize := None.
Definition max_32 (sz:wsize) := if (sz <= U32)%CMP then sz else U32.
Definition omax_32 sz := Some (max_32 sz).
Definition imm8 (sz:wsize) := Some U8.
(* FIXME: if MOV u64 addr imm : the max size is u32 *)
Definition primP op := PrimP U64 op.

(*
Inductive pp_asm_op_ext :=
  | PP_name
  | PP_iname of wsize
  | PP_iname2 of wsize & wsize
  | PP_ct of asm_arg.

Record pp_asm_op := {
  pp_aop_name : string;
  pp_aop_ext  : pp_asm_op_ext;
  pp_aop_args : seq (wsize * asm_arg);
}.
*)
Definition map_sz (sz:wsize) (a:asm_args) := List.map (fun a => (sz,a)) a.

Definition pp_name name sz args :=
  {| pp_aop_name := name;
     pp_aop_ext  := PP_name;
     pp_aop_args := map_sz sz args; |}.

Definition pp_name_ty name (ws:seq wsize) args :=
 {| pp_aop_name := name;
    pp_aop_ext  := PP_name;
    pp_aop_args := zip ws args; |}.

Definition pp_iname name sz args :=
  {| pp_aop_name := name;
     pp_aop_ext  := PP_iname sz;
     pp_aop_args := map_sz sz args; |}.

Definition pp_viname_long name ve sz args :=
  {| pp_aop_name := name;
     pp_aop_ext  := PP_viname ve true;
     pp_aop_args := map_sz sz args; |}.

Definition pp_viname name ve sz args :=
  {| pp_aop_name := name;
     pp_aop_ext  := PP_viname ve false;
     pp_aop_args := map_sz sz args; |}.

Definition pp_iname_w_8 name sz args :=
  {| pp_aop_name := name;
     pp_aop_ext  := PP_iname sz;
     pp_aop_args := zip [::sz; U8] args; |}.

Definition pp_iname_ww_8 name sz args :=
  {| pp_aop_name := name;
     pp_aop_ext  := PP_iname sz;
     pp_aop_args := zip [::sz;sz; U8] args; |}.

Definition pp_movx name szd szs args :=
  {| pp_aop_name := name;
     pp_aop_ext  := PP_iname2 szs szd;
     pp_aop_args := zip [::szs; szd] args; |}.

Definition pp_vpmovx name ve sz ve' sz' args :=
  {| pp_aop_name := name;
     pp_aop_ext  := PP_viname2 ve ve';
     pp_aop_args := zip [:: sz' ; sz ] args; |}.

Definition get_ct args :=
  match args with
  | a :: args => (PP_ct a, args)
  | _         => (PP_error, args)
  end.

Definition pp_ct name sz args :=
  let (ext, args) := get_ct args in
  {| pp_aop_name := name;
     pp_aop_ext  := ext;
     pp_aop_args := map_sz sz args; |}.


Definition pp_cqo sz (args: asm_args) :=
  let (name, ext) :=
      match sz with
      | U16 => ("cwd"%string, PP_name)
      | U32 => ("cdq"%string, PP_name)
      | U64 => ("cqo"%string, PP_name)
      | _   => ("CQO"%string, PP_error)
      end in
  {| pp_aop_name := name;
     pp_aop_ext  := ext;
     pp_aop_args := map_sz sz [::]; |}.

Definition c := [::CAcond].
Definition r := [:: CAreg].
Definition m b := [:: CAmem b].
Definition i sz := [:: CAimm sz].
Definition rm b := [:: CAreg; CAmem b].

Definition rmi sz := [:: CAreg; CAmem true; CAimm sz].
Definition ri  sz := [:: CAreg; CAimm sz].
Definition r_rm := [:: r; rm true].
Definition r_rmi sz := [:: r; rmi sz].

Definition m_ri sz := [:: m false; ri (max_32 sz)].
Definition m_r := [:: m false; r].

Definition xmm := [:: CAxmm ].
Definition xmmm b := [:: CAxmm; CAmem b].

Definition xmm_xmmm := [::xmm; xmmm true].
Definition xmmm_xmm := [::xmmm false; xmm].
Definition xmm_xmm_xmmm := [::xmm; xmm; xmmm true].


Definition check_mov sz := [:: r_rmi sz; m_ri sz]. 
Definition Ox86_MOV_instr               :=
  mk_instr_w_w "MOV" x86_MOV msb_dfl [:: E 1] [:: E 0] 2
               check_mov (fun sz => Some sz) (primP MOV) (pp_iname "mov").

Definition check_movsx (_ _:wsize) := [:: r_rm ].
Definition Ox86_MOVSX_instr             :=
  mk_instr_w_w'_10 "MOVSX" true x86_MOVSX check_movsx no_imm (PrimX MOVSX) (pp_movx "movs").
Definition Ox86_MOVZX_instr             :=
  mk_instr_w_w'_10 "MOVZX" false x86_MOVZX check_movsx no_imm (PrimX MOVZX) (pp_movx "movz").

Definition c_r_rm := [:: c; r; rm true].
Definition Ox86_CMOVcc_instr            :=
  mk_instr_bw2_w_0211 "CMOVcc" x86_CMOVcc (fun sz => [::c_r_rm]) no_imm (primP CMOVcc) (pp_ct "cmov").

Definition check_add sz := [:: m_ri (max_32 sz); r_rmi (max_32 sz)].
Definition Ox86_ADD_instr  :=
  mk_instr_w2_b5w_010 "ADD" x86_ADD check_add omax_32 (primP ADD) (pp_iname "add").
Definition Ox86_SUB_instr :=
  mk_instr_w2_b5w_010 "SUB" x86_SUB check_add omax_32 (primP SUB) (pp_iname "sub").

Definition check_mul (_:wsize) := [:: [::rm true]].
Definition Ox86_MUL_instr :=
  mk_instr_w2_b5w2 "MUL"  x86_MUL msb_dfl [:: R RAX; E 0] [:: R RDX; R RAX] 1
    check_mul no_imm (primP MUL) (pp_iname "mul").

Definition Ox86_IMUL_instr :=
  mk_instr_w2_b5w2 "IMUL" x86_IMUL msb_dfl [:: R RAX; E 0] [:: R RDX; R RAX] 1
    check_mul no_imm (primP IMUL) (pp_iname "imul") .

Definition Ox86_IMULr_instr             :=
  mk_instr_w2_b5w_010 "IMULr" x86_IMULt
    (fun _ => [::r_rm]) no_imm (primP IMULr) (pp_iname "imul").

Definition Ox86_IMULri_instr :=
  mk_instr_w2_b5w "IMULri" x86_IMULt msb_dfl [:: E 1; E 2] [:: E 0] 3
  (fun sz => [:: [::r; rm true; i (max_32 sz)]]) omax_32 (primP IMULri) (pp_iname "imul").

Definition Ox86_DIV_instr :=
  mk_instr_w3_b5w2_da0ad "DIV" Unsigned x86_DIV check_mul no_imm (primP DIV) (pp_iname "div").

Definition Ox86_IDIV_instr :=
  mk_instr_w3_b5w2_da0ad "IDIV" Signed x86_IDIV check_mul no_imm (primP IDIV) (pp_iname "idiv").

Definition Ox86_CQO_instr :=
  mk_instr_w_w "CQO" x86_CQO msb_dfl [:: R RAX] [:: R RDX] 0 (fun _ => [:: [::]]) no_imm (primP CQO) pp_cqo.

Definition Ox86_ADC_instr :=
  mk_instr_w2b_b5w_010 "ADC" x86_ADC check_add omax_32 (primP ADC) (pp_iname "adc").

Definition Ox86_SBB_instr               :=
  mk_instr_w2b_b5w_010 "SBB" x86_SBB check_add omax_32 (primP SBB) (pp_iname "sbb").

Definition check_adcx (_:wsize) := [:: r_rm].
Definition Ox86_ADCX_instr :=
  mk_instr_w2b_bw "ADCX" x86_ADCX CF check_adcx no_imm (primP ADCX) (pp_iname "adcx").

Definition Ox86_ADOX_instr :=
  mk_instr_w2b_bw "ADOX" x86_ADCX OF check_adcx no_imm (primP ADOX) (pp_iname "adox").

Definition check_mulx := [:: [::r;r;rm true]].
Definition Ox86_MULX_instr :=
  let name := "MULX"%string in
   ((fun (sz:wsize) =>
     mk_instr (pp_sz name sz) (w2_ty sz sz) (w2_ty sz sz)
         [::R RDX; E 2] [:: E 0; E 1] MSB_CLEAR
         (@x86_MULX sz) (op_leak_ty (w2_ty sz sz)) check_mulx 3 sz (no_imm sz) [::] (pp_iname name sz)),
    (name, PrimP U64 MULX)).

Definition check_neg (_:wsize) := [::[::rm false]].
Definition Ox86_NEG_instr               :=
  mk_instr_w_b5w "NEG" x86_NEG msb_dfl [:: E 0] [:: E 0] 1 check_neg no_imm (primP NEG) (pp_iname "neg").

Definition Ox86_INC_instr               :=
  mk_instr_w_b4w_00 "INC" x86_INC check_neg no_imm (primP INC) (pp_iname "inc").

Definition Ox86_DEC_instr :=
  mk_instr_w_b4w_00 "DEC" x86_DEC check_neg no_imm (primP DEC) (pp_iname "dec").

Definition Ox86_LZCNT_instr               :=
  mk_instr_w_b5w "LZCNT" x86_LZCNT msb_dfl [:: E 1] [:: E 0] 2 (fun _ => [::r_rm]) no_imm (primP LZCNT) (pp_iname "lzcnt").

Definition check_setcc := [:: [::c; rm false]].
Definition Ox86_SETcc_instr             :=
  mk_instr_pp "SETcc" b_ty w8_ty [:: E 0] [:: E 1] msb_dfl x86_SETcc (op_leak_ty (b_ty)) check_setcc 2 U8 (no_imm U8) (PrimM SETcc) (pp_ct "set" U8).

Definition check_bt (_:wsize) := [:: [::rm true; ri U8]].
Definition Ox86_BT_instr                :=
  mk_instr_w2_b "BT" x86_BT msb_dfl [:: E 0; E 1] [:: F CF] 2 check_bt imm8 (primP BT) (pp_iname_w_8 "bt").

(* -------------------------------------------------------------------- *)
Definition Ox86_CLC_instr :=
  mk_instr_pp "CLC" [::] b_ty [::] [:: F CF ] msb_dfl x86_CLC (op_leak_ty [::]) [:: [::]] 0 U8 None (PrimM CLC) (pp_name "clc" U8).

Definition Ox86_STC_instr :=
  mk_instr_pp "STC" [::] b_ty [::] [:: F CF ] msb_dfl x86_STC (op_leak_ty [::]) [:: [::]] 0 U8 None (PrimM STC) (pp_name "stc" U8).

(* -------------------------------------------------------------------- *)
Definition check_lea (_:wsize) := [:: [::r; m true]].
Definition Ox86_LEA_instr :=
  mk_instr_w_w "LEA" x86_LEA msb_dfl [:: E 1] [:: E 0] 2 check_lea no_imm (primP LEA) (pp_iname "lea").

Definition check_test (sz:wsize) := [:: [::rm false; ri (max_32 sz)]].
Definition Ox86_TEST_instr              :=
  mk_instr_w2_b5 "TEST" x86_TEST msb_dfl [:: E 0; E 1] 2 check_test omax_32 (primP TEST) (pp_iname "test").

Definition check_cmp (sz:wsize) := [:: [::rm false; ri (max_32 sz)]; r_rm].
Definition Ox86_CMP_instr :=
  mk_instr_w2_b5 "CMP" x86_CMP msb_dfl [:: E 0; E 1] 2 check_cmp omax_32 (primP CMP) (pp_iname "cmp").

Definition Ox86_AND_instr :=
  mk_instr_w2_b5w_010 "AND" x86_AND check_cmp omax_32 (primP AND) (pp_iname "and").

Definition Ox86_OR_instr                :=
  mk_instr_w2_b5w_010 "OR" x86_OR check_cmp omax_32 (primP OR) (pp_iname "or").

Definition Ox86_XOR_instr               :=
  mk_instr_w2_b5w_010 "XOR" x86_XOR check_cmp omax_32 (primP XOR) (pp_iname "xor").

Definition check_andn (_:wsize) := [:: [:: r; r; rm true]].
Definition Ox86_ANDN_instr              :=
  mk_instr_w2_b5w "ANDN" x86_ANDN msb_dfl [:: E 1; E 2] [:: E 0] 3
  check_andn no_imm (primP ANDN) (pp_iname "andn").

Definition Ox86_NOT_instr               :=
  mk_instr_w_w "NOT" x86_NOT msb_dfl [:: E 0] [:: E 0] 1 check_neg no_imm (primP NOT) (pp_iname "not").

Definition check_ror (_:wsize):= [::[::rm false; ri U8]].
Definition Ox86_ROR_instr               :=
  mk_instr_ww8_b2w_0c0 "ROR" x86_ROR check_ror imm8 (primP ROR) (pp_iname_w_8 "ror").

Definition Ox86_ROL_instr :=
  mk_instr_ww8_b2w_0c0 "ROL" x86_ROL check_ror imm8 (primP ROL) (pp_iname_w_8 "rol").

Definition Ox86_RCR_instr :=
  mk_instr_ww8b_b2w_0c0 "RCR" x86_RCR check_ror imm8 (primP RCR) (pp_iname_w_8 "rcr").

Definition Ox86_RCL_instr :=
  mk_instr_ww8b_b2w_0c0 "RCL" x86_RCL check_ror imm8 (primP RCL) (pp_iname_w_8 "rcl").

Definition Ox86_SHL_instr :=
  mk_instr_ww8_b5w_0c0 "SHL" x86_SHL check_ror imm8 (primP SHL) (pp_iname_w_8 "shl").

Definition Ox86_SHR_instr :=
  mk_instr_ww8_b5w_0c0 "SHR" x86_SHR check_ror imm8 (primP SHR) (pp_iname_w_8 "shr").

Definition Ox86_SAL_instr :=
  mk_instr_ww8_b5w_0c0 "SAL" x86_SHL check_ror imm8 (primP SAL) (pp_iname_w_8 "sal").

Definition Ox86_SAR_instr :=
  mk_instr_ww8_b5w_0c0 "SAR" x86_SAR check_ror imm8 (primP SAR) (pp_iname_w_8 "sar").

Definition check_shld (_:wsize):= [::[::rm false; r; ri U8]].
Definition Ox86_SHLD_instr :=
  mk_instr_w2w8_b5w_01c0 "SHLD" x86_SHLD check_shld imm8 (primP SHLD) (pp_iname_ww_8 "shld").

Definition Ox86_SHRD_instr :=
  mk_instr_w2w8_b5w_01c0 "SHRD" x86_SHRD check_shld imm8 (primP SHRD) (pp_iname_ww_8 "shrd").

Definition Ox86_BSWAP_instr :=
  mk_instr_w_w "BSWAP" x86_BSWAP msb_dfl [:: E 0] [:: E 0] 1 (fun _ => [:: [::r]]) no_imm (primP BSWAP) (pp_iname "bswap").

Definition Ox86_POPCNT_instr :=
  mk_instr_w_b5w "POPCNT" x86_POPCNT msb_dfl [:: E 1] [:: E 0] 2 (fun _ => [::r_rm]) no_imm (primP POPCNT) (pp_name "popcnt").

Definition Ox86_PEXT_instr :=
  mk_instr_w2_w_120 "PEXT" x86_PEXT (fun _ => [:: [:: r; r; rm true]]) no_imm (primP PEXT) (pp_name "pext").

(* Vectorized instruction *)

Definition pp_movd name sz args :=
 pp_name_ty (if sz == U64 then (name ++ "q")%string else (name ++ "d")%string)
            ([::U128; sz]) args.

Definition check_movd (_:wsize) := [:: [::xmm; rm true]].
Definition Ox86_MOVD_instr :=
  mk_instr_w_w128_10 "MOVD" MSB_MERGE x86_MOVD check_movd no_imm (primP MOVD) (pp_movd "mov").

Definition Ox86_VMOV_instr :=
  mk_instr_w_w128_10 "VMOV" MSB_CLEAR x86_MOVD check_movd no_imm (primP VMOV) (pp_movd "vmov").

Definition check_vmovdqu (_:wsize) := [:: xmm_xmmm; xmmm_xmm].
Definition Ox86_VMOVDQU_instr :=
  mk_instr_w_w "VMOVDQU" x86_VMOVDQU MSB_CLEAR [:: E 1] [:: E 0] 2 check_vmovdqu no_imm (PrimP U128 VMOVDQU) (pp_name "vmovdqu").

Definition Ox86_VPMOVSX_instr :=
  let name := "VPMOVSX"%string in
  (λ ve sz ve' sz',
   mk_instr (pp_ve_sz_ve_sz name ve sz ve' sz') [:: sword sz ] [:: sword sz' ] [:: E 1 ] [:: E 0 ]
            MSB_CLEAR (@x86_VPMOVSX ve sz ve' sz') (op_leak_ty  [:: sword sz ]) [:: [:: xmm ; xmmm true]] 2 sz None [::] (pp_vpmovx "vpmovsx" ve sz ve' sz'),
   (name, PrimVV VPMOVSX)
   ).

Definition Ox86_VPMOVZX_instr :=
  let name := "VPMOVZX"%string in
  (λ ve sz ve' sz',
   mk_instr (pp_ve_sz_ve_sz name ve sz ve' sz') [:: sword sz ] [:: sword sz' ] [:: E 1 ] [:: E 0 ]
            MSB_CLEAR (@x86_VPMOVZX ve sz ve' sz')  (op_leak_ty  [:: sword sz ]) [:: [:: xmm ; xmmm true]] 2 sz None [::] (pp_vpmovx "vpmovzx" ve sz ve' sz'),
   (name, PrimVV VPMOVZX)
   ).

Definition check_xmm_xmm_xmmm (_:wsize) := [:: xmm_xmm_xmmm].

Definition Ox86_VPAND_instr  := mk_instr_w2_w_120    "VPAND"   x86_VPAND  check_xmm_xmm_xmmm no_imm (PrimP U128 VPAND) (pp_name "vpand").
Definition Ox86_VPANDN_instr := mk_instr_w2_w_120    "VPANDN"  x86_VPANDN check_xmm_xmm_xmmm no_imm (PrimP U128 VPANDN) (pp_name "vpandn").
Definition Ox86_VPOR_instr   := mk_instr_w2_w_120    "VPOR"    x86_VPOR   check_xmm_xmm_xmmm no_imm (PrimP U128 VPOR) (pp_name "vpor").
Definition Ox86_VPXOR_instr  := mk_instr_w2_w_120    "VPXOR"   x86_VPXOR  check_xmm_xmm_xmmm no_imm (PrimP U128 VPXOR) (pp_name "vpxor").
Definition Ox86_VPADD_instr  := mk_ve_instr_w2_w_120 "VPADD"   x86_VPADD  check_xmm_xmm_xmmm no_imm (PrimV VPADD) (pp_viname "vpadd").
Definition Ox86_VPSUB_instr  := mk_ve_instr_w2_w_120 "VPSUB"   x86_VPSUB  check_xmm_xmm_xmmm no_imm (PrimV VPSUB) (pp_viname "vpsub").

Definition Ox86_VPMULL_instr := mk_ve_instr_w2_w_120 "VPMULL" x86_VPMULL check_xmm_xmm_xmmm no_imm (PrimV VPMULL) (pp_viname "vpmull").
Definition Ox86_VPMULU_instr := ((fun sz => mk_instr (pp_sz "VPMULU" sz) (w2_ty sz sz) (w_ty sz) [:: E 1 ; E 2] [:: E 0] MSB_CLEAR (@x86_VPMULU sz)  (op_leak_ty (w2_ty sz sz)) (check_xmm_xmm_xmmm sz) 3 sz (no_imm sz) [::] (pp_name "vpmuludq" sz)), ("VPMULU"%string, (PrimP U128 VPMULU))).

Definition Ox86_VPMULH_instr := mk_ve_instr_w2_w_120 "VPMULH" x86_VPMULH check_xmm_xmm_xmmm no_imm (PrimV VPMULH) (pp_viname "vpmulh").
Definition Ox86_VPMULHU_instr := mk_ve_instr_w2_w_120 "VPMULHU" x86_VPMULHU check_xmm_xmm_xmmm no_imm (PrimV VPMULHU) (pp_viname "vpmulhu").

Definition Ox86_VPMULHRS_instr := mk_ve_instr_w2_w_120 "VPMULHRS" x86_VPMULHRS check_xmm_xmm_xmmm no_imm (PrimV VPMULHRS) (pp_viname "vpmulhrs").

Definition check_vpextr (_:wsize) :=  [:: [:: rm false; xmm; i U8] ].

Definition pp_viname_t name ve (ts:seq wsize) args :=
  {| pp_aop_name := name;
     pp_aop_ext  := PP_viname ve false;
     pp_aop_args := zip ts args; |}.

Definition Ox86_VPEXTR_instr :=
  ((fun sz =>
      let ve := if sz == U32 then  VE32 else VE64 in
      mk_instr (pp_sz "VPEXTR" sz) w128w8_ty (w_ty sz) [:: E 1 ; E 2] [:: E 0] msb_dfl (@x86_VPEXTR sz) (op_leak_ty w128w8_ty)
                       (check_vpextr sz) 3 U128 (imm8 U128) [::]
                       (pp_viname_t "vpextr" ve [:: sz; U128; U8])),
    ("VPEXTR"%string, (primP VPEXTR))).

Definition pp_vpinsr ve args :=
  let rs := match ve with VE8 | VE16 | VE32 => U32 | VE64 => U64 end in
  {| pp_aop_name := "vpinsr";
     pp_aop_ext  := PP_viname ve false;
     pp_aop_args := zip [::U128; U128; rs; U8] args; |}.

Definition check_vpinsr (_:wsize) :=  [:: [:: xmm; xmm; rm true; i U8] ].
Definition Ox86_VPINSR_instr  :=
  ((fun (sz:velem) => mk_instr (pp_ve_sz "VPINSR" sz U128) (w128ww8_ty sz) w128_ty [:: E 1 ; E 2 ; E 3] [:: E 0] MSB_CLEAR (x86_VPINSR sz)
                      (op_leak_ty (w128ww8_ty sz)) (check_vpinsr sz) 4 U128 (imm8 sz) [::] (pp_vpinsr sz)),
   ("VPINSR"%string, PrimV (fun ve _ => VPINSR ve))).

Definition check_xmm_xmm_imm8 (_:wsize) := [:: [:: xmm; xmm; i U8]].
Definition Ox86_VPSLL_instr :=
  mk_ve_instr_ww8_w_120 "VPSLL" x86_VPSLL check_xmm_xmm_imm8 imm8 (PrimV VPSLL) (pp_viname "vpsll").

Definition Ox86_VPSRL_instr :=
  mk_ve_instr_ww8_w_120 "VPSRL" x86_VPSRL check_xmm_xmm_imm8 imm8 (PrimV VPSRL) (pp_viname "vpsrl").

Definition Ox86_VPSRA_instr :=
  mk_ve_instr_ww8_w_120 "VPSRA" x86_VPSRA check_xmm_xmm_imm8 imm8 (PrimV VPSRA) (pp_viname "vpsra").

Definition Ox86_VPSLLV_instr :=
  mk_ve_instr_w2_w_120 "VPSLLV" x86_VPSLLV check_xmm_xmm_xmmm no_imm (PrimV VPSLLV) (pp_viname "vpsllv").

Definition Ox86_VPSRLV_instr :=
  mk_ve_instr_w2_w_120 "VPSRLV" x86_VPSRLV check_xmm_xmm_xmmm no_imm (PrimV VPSRLV) (pp_viname "vpsrlv").

Definition Ox86_VPSLLDQ_instr :=
  mk_instr_ww8_w_120 "VPSLLDQ" x86_VPSLLDQ check_xmm_xmm_imm8 imm8 (PrimP U128 VPSLLDQ) (pp_name "vpslldq").

Definition Ox86_VPSRLDQ_instr :=
  mk_instr_ww8_w_120 "VPSRLDQ" x86_VPSRLDQ check_xmm_xmm_imm8 imm8 (PrimP U128 VPSRLDQ) (pp_name "vpsrldq").

Definition Ox86_VPSHUFB_instr :=
  mk_instr_w2_w_120 "VPSHUFB" x86_VPSHUFB check_xmm_xmm_xmmm no_imm (PrimP U128 VPSHUFB) (pp_name "vpshufb").

Definition check_xmm_xmmm_imm8 (_:wsize) := [:: [:: xmm; xmmm true; i U8]].
Definition Ox86_VPSHUFHW_instr          :=
  mk_instr_ww8_w_120 "VPSHUFHW" x86_VPSHUFHW check_xmm_xmmm_imm8 imm8 (PrimP U128 VPSHUFHW) (pp_name "vpshufhw").

Definition Ox86_VPSHUFLW_instr :=
  mk_instr_ww8_w_120 "VPSHUFLW" x86_VPSHUFLW check_xmm_xmmm_imm8 imm8 (PrimP U128 VPSHUFLW) (pp_name "vpshuflw").

Definition Ox86_VPSHUFD_instr :=
  mk_instr_ww8_w_120 "VPSHUFD" x86_VPSHUFD check_xmm_xmmm_imm8 imm8 (PrimP U128 VPSHUFD) (pp_name "vpshufd").

Definition Ox86_VPUNPCKH_instr :=
  mk_ve_instr_w2_w_120 "VPUNPCKH" x86_VPUNPCKH check_xmm_xmm_xmmm no_imm (PrimV VPUNPCKH) (pp_viname_long "vpunpckh").

Definition Ox86_VPUNPCKL_instr :=
  mk_ve_instr_w2_w_120 "VPUNPCKL" x86_VPUNPCKL check_xmm_xmm_xmmm no_imm (PrimV VPUNPCKL) (pp_viname_long "vpunpckl").

Definition check_xmm_xmm_xmmm_imm8 (_:wsize) := [:: [:: xmm; xmm; xmmm true; i U8]].
Definition Ox86_VPBLENDD_instr :=
  mk_instr_w2w8_w_1230 "VPBLENDD" x86_VPBLENDD check_xmm_xmm_xmmm_imm8 imm8 (PrimP U128 VPBLENDD) (pp_name "vpblendd").

Definition Ox86_VSHUFPS_instr := 
  mk_instr_w2w8_w_1230 "VSHUFPS" x86_VSHUFPS check_xmm_xmm_xmmm_imm8 imm8 (PrimP U128 VSHUFPS)
      (pp_name "vshufps").                 

Definition pp_vpbroadcast ve sz args :=
  {| pp_aop_name := "vpbroadcast";
     pp_aop_ext  := PP_viname ve false;
     pp_aop_args := zip [::sz; U128] args; |}.

Definition check_xmm_xmmm (_:wsize) := [:: [:: xmm; xmmm true]].

Definition Ox86_VPBROADCAST_instr       :=
  mk_ve_instr_w_w_10 "VPBROADCAST" x86_VPBROADCAST check_xmm_xmmm no_imm (PrimV VPBROADCAST) pp_vpbroadcast.

Definition Ox86_VMOVSHDUP_instr :=
  mk_ve_instr_w_w_10 "VMOVSHDUP" x86_VMOVSHDUP check_xmm_xmmm no_imm (PrimV VMOVSHDUP) (λ _, pp_name "vmovshdup").

Definition Ox86_VMOVSLDUP_instr :=
  mk_ve_instr_w_w_10 "VMOVSLDUP" x86_VMOVSLDUP check_xmm_xmmm no_imm (PrimV VMOVSLDUP) (λ _, pp_name "vmovsldup").

Definition Ox86_VPALIGNR_instr := 
  ((fun sz =>
     mk_instr (pp_sz "VPALIGNR" sz) (w2w8_ty sz) (w_ty sz) [:: E 1 ; E 2 ; E 3] [:: E 0] MSB_CLEAR 
      (@x86_VPALIGNR sz) (op_leak_ty (w2w8_ty sz)) (check_xmm_xmm_xmmm_imm8 sz) 4 sz (imm8 sz) [::] (pp_name "vpalignr" sz)), ("VPALIGNR"%string, PrimP U128 VPALIGNR)).

(* 256 *)

Definition Ox86_VBROADCASTI128_instr    :=
  (mk_instr (pp_s "VPBROADCAST_2u128") w128_ty w256_ty [:: E 1] [:: E 0] MSB_CLEAR (x86_VPBROADCAST U256) (op_leak_ty w128_ty)
            ([:: [::xmm; m true]]) 2 U256 (no_imm U256) [::] (pp_name_ty "vbroadcasti128" [::U256; U128]),
   ("VPBROADCAST_2u128"%string, (PrimM VBROADCASTI128))).

Definition check_xmmm_xmm_imm8 (_:wsize) := [:: [:: xmmm false; xmm; i U8]].

Definition Ox86_VEXTRACTI128_instr :=
  mk_instr_pp "VEXTRACTI128" w256w8_ty w128_ty [:: E 1; E 2] [:: E 0] MSB_CLEAR x86_VEXTRACTI128 (op_leak_ty w256w8_ty)
              (check_xmmm_xmm_imm8 U256) 3 U256 (imm8 U256) (PrimM VEXTRACTI128) (pp_name_ty "vextracti128" [::U128; U256; U8]).

Definition Ox86_VINSERTI128_instr :=
  mk_instr_pp "VINSERTI128" w256w128w8_ty w256_ty [:: E 1; E 2; E 3] [:: E 0] MSB_CLEAR x86_VINSERTI128 (op_leak_ty w256w128w8_ty)
              (check_xmm_xmm_xmmm_imm8 U256) 4 U256 (imm8 U256) (PrimM VINSERTI128) (pp_name_ty "vinserti128" [::U256;U256; U128; U8]).

Definition Ox86_VPERM2I128_instr :=
  mk_instr_pp "VPERM2I128" w256x2w8_ty w256_ty [:: E 1; E 2; E 3] [:: E 0] MSB_CLEAR x86_VPERM2I128 (op_leak_ty w256x2w8_ty)
              (check_xmm_xmm_xmmm_imm8 U256) 4 U256 (imm8 U256) (PrimM VPERM2I128) (pp_name_ty "vperm2i128" [::U256;U256;U256;U8]).

Definition Ox86_VPERMD_instr :=
  mk_instr_pp "VPERMD" (w2_ty U256 U256) w256_ty [:: E 1; E 2] [:: E 0] MSB_CLEAR x86_VPERMD (op_leak_ty (w2_ty U256 U256))
       (check_xmm_xmm_xmmm U256) 3 U256 None (PrimM VPERMD) (pp_name "vpermd" U256).

Definition Ox86_VPERMQ_instr :=
  mk_instr_pp "VPERMQ" w256w8_ty w256_ty [:: E 1; E 2] [:: E 0] MSB_CLEAR x86_VPERMQ  (op_leak_ty w256w8_ty)
              (check_xmm_xmmm_imm8 U256) 3 U256 (imm8 U256) (PrimM VPERMQ) (pp_name_ty "vpermq" [::U256;U256;U8]).

Definition Ox86_PMOVMSKB_instr :=
  (fun ssz dsz => mk_instr
    (pp_sz_sz "VPMOVMSKB"%string false ssz dsz) (* Jasmin name *)
    (w_ty ssz) (* args type *)
    (w_ty dsz) (* result type *)
    [:: E 1 ] (* args *)
    [:: E 0 ]  (* results *)
    MSB_CLEAR (* clear MostSignificantBits *)
    (@x86_VPMOVMSKB ssz dsz) (* semantics *)
    (op_leak_ty (w_ty ssz))
    [:: [:: r ; xmm ] ] (* arg checks *)
    2 (* nargs *)
    ssz (* size *)
    None (* no immediate arg. *)
    [::]
    (pp_name_ty "vpmovmskb" [:: dsz; ssz]) (* asm pprinter *)
  , ("VPMOVMSKB"%string, PrimX VPMOVMSKB) (* jasmin concrete syntax *)
  ).

Definition Ox86_VPCMPEQ_instr :=
  (fun (ve: velem) sz => mk_instr
                  (pp_ve_sz "VPCMPEQ"%string ve sz)
                  (w2_ty sz sz)
                  (w_ty sz)
                  [:: E 1; E 2]
                  [:: E 0]
                  MSB_CLEAR
                  (@x86_VPCMPEQ ve sz)
                  (op_leak_ty (w2_ty sz sz))
                  (check_xmm_xmm_xmmm sz)
                  3
                  sz
                  None
                  [::]
                  (pp_viname "vpcmpeq" ve sz)
                ,("VPCMPEQ"%string, PrimV VPCMPEQ)
  ).

Definition Ox86_VPCMPGT_instr :=
  (fun (ve: velem) sz => mk_instr
                  (pp_ve_sz "VPCMPGT"%string ve sz)
                  (w2_ty sz sz)
                  (w_ty sz)
                  [:: E 1; E 2]
                  [:: E 0]
                  MSB_CLEAR
                  (@x86_VPCMPGT ve sz)
                  (op_leak_ty (w2_ty sz sz))
                  (check_xmm_xmm_xmmm sz)
                  3
                  sz
                  None
                  [::]
                  (pp_viname "vpcmpgt" ve sz)
                ,("VPCMPGT"%string, PrimV VPCMPGT)
  ).

Definition Ox86_VPMADDUBSW_instr :=
  (fun sz => mk_instr
                (pp_sz "VPMADDUBSW"%string sz)
                (w2_ty sz sz)
                (w_ty sz)
                [:: E 1; E 2]
                [:: E 0 ]
                MSB_CLEAR
                (@x86_VPMADDUBSW sz)
                (op_leak_ty (w2_ty sz sz))
                (check_xmm_xmm_xmmm sz)
                3
                sz
                (no_imm sz)
                [::]
                (pp_name_ty "vpmaddubsw" [:: sz; sz; sz])
             ,("VPMADDUBSW"%string, PrimP U128 VPMADDUBSW)
  ).

Definition Ox86_VPMADDWD_instr :=
  (fun sz => mk_instr
                (pp_sz "VPMADDWD"%string sz)
                (w2_ty sz sz)
                (w_ty sz)
                [:: E 1; E 2]
                [:: E 0 ]
                MSB_CLEAR
                (@x86_VPMADDWD sz)
                (op_leak_ty (w2_ty sz sz))
                (check_xmm_xmm_xmmm sz)
                3
                sz
                (no_imm sz)
                [::]
                (pp_name_ty "vpmaddwd" [:: sz; sz; sz])
             ,("VPMADDWD"%string, PrimP U128 VPMADDWD)
  ).

Definition check_movpd := [:: [::m false; xmm]].

Definition Ox86_VMOVLPD_instr :=
  mk_instr_pp "VMOVLPD" (w_ty U128) (w_ty U64) [:: E 1] [:: E 0] MSB_CLEAR x86_VMOVLPD (op_leak_ty (w_ty U128)) check_movpd 2 U64 None (PrimM VMOVLPD) (pp_name_ty "vmovlpd" [::U64; U128]).

Definition Ox86_VMOVHPD_instr :=
  mk_instr_pp "VMOVHPD" (w_ty U128) (w_ty U64) [:: E 1] [:: E 0] MSB_CLEAR x86_VMOVHPD (op_leak_ty (w_ty U128)) check_movpd 2 U64 None (PrimM VMOVHPD) (pp_name_ty "vmovhpd" [::U64;U128]).

(* Monitoring instructions.
   These instructions are declared for the convenience of the programmer.
   Nothing can be proved about programs that use these instructions;
   in particular the correctness theorem does not apply to programs using them. *)

Definition Ox86_RDTSC_instr :=
  (fun sz => mk_instr
              (pp_sz "RDTSC"%string sz) (* Jasmin name *)
              nil (* args type *)
              (w2_ty sz sz) (* result type *)
              nil (* args *)
              [:: R RDX; R RAX] (* results *)
              MSB_CLEAR (* clear MostSignificantBits *)
              (Error ErrType) (* No semantics *)
              (λ _, Error ErrType)
              [:: [::]]
              0 (* nargs *)
              sz (* size *)
              None (* no immediate arg. *)
              [::]
              (pp_name_ty "rdtsc" [:: sz; sz]) (* asm pretty-print*)
   ,("RDTSC"%string, PrimP U64 RDTSC) (* jasmin concrete syntax *)
  ).

Definition Ox86_RDTSCP_instr :=
  (fun sz => mk_instr
              (pp_sz "RDTSCP"%string sz) (* Jasmin name *)
              nil (* args type *)
              (w3_ty sz) (* result type *)
              nil (* args *)
              [:: R RDX; R RAX; R RCX] (* results *)
              MSB_CLEAR (* clear MostSignificantBits *)
              (Error ErrType) (* No semantics *)
              (λ _, Error ErrType)
              [:: [::]] (* arg checks *)
              0 (* nargs *)
              sz (* size *)
              None (* no immediate arg. *)
              [::]
              (pp_name_ty "rdtscp" [:: sz; sz; sz]) (* asm pprinter *)
   ,("RDTSCP"%string, PrimP U64 RDTSCP) (* jasmin concrete syntax *)
  ).

(* AES instructions *)
Definition mk_instr_aes2 jname aname constr x86_sem msb_flag :=
  mk_instr_pp jname (w2_ty U128 U128) (w_ty U128) [:: E 0; E 1] [:: E 0] msb_flag x86_sem  (op_leak_ty (w2_ty U128 U128))
         (check_xmm_xmmm U128) 2 U128 (imm8 U128) (PrimM constr) (pp_name_ty aname [::U128;U128]).

Definition mk_instr_aes3 jname aname constr x86_sem msb_flag :=
  mk_instr_pp jname (w2_ty U128 U128) (w_ty U128) [:: E 1; E 2] [:: E 0] msb_flag x86_sem  (op_leak_ty (w2_ty U128 U128))
         (check_xmm_xmm_xmmm U128) 3 U128 (imm8 U128) (PrimM constr) (pp_name_ty aname [::U128;U128;U128]).

Definition Ox86_AESDEC_instr := 
  mk_instr_aes2 "AESDEC" "aesdec" AESDEC x86_AESDEC MSB_MERGE.

Definition Ox86_VAESDEC_instr := 
  mk_instr_aes3 "VAESDEC" "vaesdec" VAESDEC x86_AESDEC MSB_CLEAR.

Definition Ox86_AESDECLAST_instr := 
  mk_instr_aes2 "AESDECLAST" "aesdeclast" AESDECLAST x86_AESDECLAST MSB_MERGE.

Definition Ox86_VAESDECLAST_instr := 
  mk_instr_aes3 "VAESDECLAST" "vaesdeclast" VAESDECLAST x86_AESDECLAST MSB_CLEAR.

Definition Ox86_AESENC_instr := 
  mk_instr_aes2 "AESENC" "aesenc" AESENC x86_AESENC MSB_MERGE.

Definition Ox86_VAESENC_instr := 
  mk_instr_aes3 "VAESENC" "vaesenc" VAESENC x86_AESENC MSB_CLEAR.

Definition Ox86_AESENCLAST_instr := 
  mk_instr_aes2 "AESENCLAST" "aesenclast" AESENCLAST x86_AESENCLAST MSB_MERGE.

Definition Ox86_VAESENCLAST_instr := 
  mk_instr_aes3 "VAESENCLAST" "vaesenclast" VAESENCLAST x86_AESENCLAST MSB_CLEAR.

Definition Ox86_AESIMC_instr := 
  mk_instr_pp "AESIMC" (w_ty U128) (w_ty U128) [:: E 1] [:: E 0] MSB_MERGE x86_AESIMC  (op_leak_ty (w_ty U128))
         (check_xmm_xmmm U128) 2 U128 (imm8 U128) (PrimM AESIMC) (pp_name_ty "aesimc" [::U128;U128]).

Definition Ox86_VAESIMC_instr := 
  mk_instr_pp "VAESIMC" (w_ty U128) (w_ty U128) [:: E 1] [:: E 0] MSB_CLEAR x86_AESIMC  (op_leak_ty (w_ty U128))
         (check_xmm_xmmm U128) 2 U128 (imm8 U128) (PrimM VAESIMC) (pp_name_ty "vaesimc" [::U128;U128]).

Definition Ox86_AESKEYGENASSIST_instr := 
  mk_instr_pp "AESKEYGENASSIST" (w2_ty U128 U8) (w_ty U128) [:: E 1; E 2] [:: E 0] 
    MSB_MERGE x86_AESKEYGENASSIST  (op_leak_ty (w2_ty U128 U8))
   (check_xmm_xmmm_imm8 U128) 3 U128 (imm8 U8) (PrimM AESKEYGENASSIST) 
   (pp_name_ty "aeskeygenassist" [::U128;U128;U8]).

Definition Ox86_VAESKEYGENASSIST_instr := 
  mk_instr_pp "VAESKEYGENASSIST" (w2_ty U128 U8) (w_ty U128) [:: E 1; E 2] [:: E 0] 
    MSB_CLEAR x86_AESKEYGENASSIST (op_leak_ty (w2_ty U128 U8))
   (check_xmm_xmmm_imm8 U128) 3 U128 (imm8 U8) (PrimM VAESKEYGENASSIST) 
   (pp_name_ty "vaeskeygenassist" [::U128;U128;U8]).

Definition instr_desc o : instr_desc_t :=
  match o with
  | MOV sz             => Ox86_MOV_instr.1 sz
  | MOVSX sz sz'       => Ox86_MOVSX_instr.1 sz sz'
  | MOVZX sz sz'       => Ox86_MOVZX_instr.1 sz sz'
  | CMOVcc sz          => Ox86_CMOVcc_instr.1 sz
  | BSWAP sz           => Ox86_BSWAP_instr.1 sz
  | POPCNT sz          => Ox86_POPCNT_instr.1 sz
  | PEXT sz            => Ox86_PEXT_instr.1 sz
  | CQO sz             => Ox86_CQO_instr.1 sz
  | ADD sz             => Ox86_ADD_instr.1 sz
  | SUB sz             => Ox86_SUB_instr.1 sz
  | MUL sz             => Ox86_MUL_instr.1 sz
  | IMUL sz            => Ox86_IMUL_instr.1 sz
  | IMULr sz           => Ox86_IMULr_instr.1 sz
  | IMULri sz          => Ox86_IMULri_instr.1 sz
  | DIV sz             => Ox86_DIV_instr.1 sz
  | IDIV sz            => Ox86_IDIV_instr.1 sz
  | ADC sz             => Ox86_ADC_instr.1 sz
  | ADCX sz            => Ox86_ADCX_instr.1 sz
  | ADOX sz            => Ox86_ADOX_instr.1 sz
  | MULX sz            => Ox86_MULX_instr.1 sz
  | SBB sz             => Ox86_SBB_instr.1 sz
  | NEG sz             => Ox86_NEG_instr.1 sz
  | INC sz             => Ox86_INC_instr.1 sz
  | DEC sz             => Ox86_DEC_instr.1 sz
  | LZCNT sz           => Ox86_LZCNT_instr.1 sz
  | SETcc              => Ox86_SETcc_instr.1
  | BT sz              => Ox86_BT_instr.1 sz
  | CLC                => Ox86_CLC_instr.1
  | STC                => Ox86_STC_instr.1
  | LEA sz             => Ox86_LEA_instr.1 sz
  | TEST sz            => Ox86_TEST_instr.1 sz
  | CMP sz             => Ox86_CMP_instr.1 sz
  | AND sz             => Ox86_AND_instr.1 sz
  | ANDN sz            => Ox86_ANDN_instr.1 sz
  | OR sz              => Ox86_OR_instr.1 sz
  | XOR sz             => Ox86_XOR_instr.1 sz
  | NOT sz             => Ox86_NOT_instr.1 sz
  | ROL sz             => Ox86_ROL_instr.1 sz
  | ROR sz             => Ox86_ROR_instr.1 sz
  | RCL sz             => Ox86_RCL_instr.1 sz
  | RCR sz             => Ox86_RCR_instr.1 sz
  | SHL sz             => Ox86_SHL_instr.1 sz
  | SHR sz             => Ox86_SHR_instr.1 sz
  | SAR sz             => Ox86_SAR_instr.1 sz
  | SAL sz             => Ox86_SAL_instr.1 sz
  | SHLD sz            => Ox86_SHLD_instr.1 sz
  | SHRD sz            => Ox86_SHRD_instr.1 sz
  | MOVD sz            => Ox86_MOVD_instr.1 sz
  | VMOV sz            => Ox86_VMOV_instr.1 sz
  | VPINSR sz          => Ox86_VPINSR_instr.1 sz
  | VEXTRACTI128       => Ox86_VEXTRACTI128_instr.1
  | VMOVDQU sz         => Ox86_VMOVDQU_instr.1 sz
  | VPMOVSX ve sz ve' sz' => Ox86_VPMOVSX_instr.1 ve sz ve' sz'
  | VPMOVZX ve sz ve' sz' => Ox86_VPMOVZX_instr.1 ve sz ve' sz'
  | VPAND sz           => Ox86_VPAND_instr.1 sz
  | VPANDN sz          => Ox86_VPANDN_instr.1 sz
  | VPOR sz            => Ox86_VPOR_instr.1 sz
  | VPXOR sz           => Ox86_VPXOR_instr.1 sz
  | VPADD sz sz'       => Ox86_VPADD_instr.1 sz sz'
  | VPSUB sz sz'       => Ox86_VPSUB_instr.1 sz sz'
  | VPMULL sz sz'      => Ox86_VPMULL_instr.1 sz sz'
  | VPMULU sz          => Ox86_VPMULU_instr.1 sz
  | VPMULH ve sz       => Ox86_VPMULH_instr.1 ve sz
  | VPMULHU ve sz      => Ox86_VPMULHU_instr.1 ve sz
  | VPMULHRS ve sz     => Ox86_VPMULHRS_instr.1 ve sz
  | VPSLL sz sz'       => Ox86_VPSLL_instr.1 sz sz'
  | VPSRL sz sz'       => Ox86_VPSRL_instr.1 sz sz'
  | VPSRA sz sz'       => Ox86_VPSRA_instr.1 sz sz'
  | VPSLLV sz sz'      => Ox86_VPSLLV_instr.1 sz sz'
  | VPSRLV sz sz'      => Ox86_VPSRLV_instr.1 sz sz'
  | VPSLLDQ sz         => Ox86_VPSLLDQ_instr.1 sz
  | VPSRLDQ sz         => Ox86_VPSRLDQ_instr.1 sz
  | VPSHUFB sz         => Ox86_VPSHUFB_instr.1 sz
  | VPSHUFHW sz        => Ox86_VPSHUFHW_instr.1 sz
  | VPSHUFLW sz        => Ox86_VPSHUFLW_instr.1 sz
  | VPSHUFD sz         => Ox86_VPSHUFD_instr.1 sz
  | VSHUFPS sz         => Ox86_VSHUFPS_instr.1 sz
  | VPUNPCKH sz sz'    => Ox86_VPUNPCKH_instr.1 sz sz'
  | VPUNPCKL sz sz'    => Ox86_VPUNPCKL_instr.1 sz sz'
  | VPBLENDD sz        => Ox86_VPBLENDD_instr.1 sz
  | VPBROADCAST sz sz' => Ox86_VPBROADCAST_instr.1 sz sz'
  | VMOVSHDUP sz sz'   => Ox86_VMOVSHDUP_instr.1 sz sz'
  | VMOVSLDUP sz sz'   => Ox86_VMOVSLDUP_instr.1 sz sz'
  | VPALIGNR sz        => Ox86_VPALIGNR_instr.1 sz 
  | VBROADCASTI128     => Ox86_VBROADCASTI128_instr.1
  | VPERM2I128         => Ox86_VPERM2I128_instr.1
  | VPERMD             => Ox86_VPERMD_instr.1
  | VPERMQ             => Ox86_VPERMQ_instr.1
  | VINSERTI128        => Ox86_VINSERTI128_instr.1
  | VPEXTR ve          => Ox86_VPEXTR_instr.1 ve
  | VPMOVMSKB sz sz'   => Ox86_PMOVMSKB_instr.1 sz sz'
  | VPCMPEQ ve sz      => Ox86_VPCMPEQ_instr.1 ve sz
  | VPCMPGT ve sz      => Ox86_VPCMPGT_instr.1 ve sz
  | VPMADDUBSW sz      => Ox86_VPMADDUBSW_instr.1 sz
  | VPMADDWD sz        => Ox86_VPMADDWD_instr.1 sz
  | VMOVLPD            => Ox86_VMOVLPD_instr.1
  | VMOVHPD            => Ox86_VMOVHPD_instr.1
  | RDTSC sz           => Ox86_RDTSC_instr.1 sz
  | RDTSCP sz          => Ox86_RDTSCP_instr.1 sz
  | AESDEC             => Ox86_AESDEC_instr.1          
  | VAESDEC            => Ox86_VAESDEC_instr.1         
  | AESDECLAST         => Ox86_AESDECLAST_instr.1      
  | VAESDECLAST        => Ox86_VAESDECLAST_instr.1     
  | AESENC             => Ox86_AESENC_instr.1          
  | VAESENC            => Ox86_VAESENC_instr.1         
  | AESENCLAST         => Ox86_AESENCLAST_instr.1      
  | VAESENCLAST        => Ox86_VAESENCLAST_instr.1     
  | AESIMC             => Ox86_AESIMC_instr.1          
  | VAESIMC            => Ox86_VAESIMC_instr.1         
  | AESKEYGENASSIST    => Ox86_AESKEYGENASSIST_instr.1 
  | VAESKEYGENASSIST   => Ox86_VAESKEYGENASSIST_instr.1 
  end.

(* -------------------------------------------------------------------- *)

Definition prim_string :=
 [::
   Ox86_MOV_instr.2;
   Ox86_MOVSX_instr.2;
   Ox86_MOVZX_instr.2;
   Ox86_CMOVcc_instr.2;
   Ox86_BSWAP_instr.2;
   Ox86_POPCNT_instr.2;
   Ox86_PEXT_instr.2;
   Ox86_CQO_instr.2;
   Ox86_ADD_instr.2;
   Ox86_SUB_instr.2;
   Ox86_MUL_instr.2;
   Ox86_IMUL_instr.2;
   Ox86_IMULr_instr.2;
   Ox86_IMULri_instr.2;
   Ox86_DIV_instr.2;
   Ox86_IDIV_instr.2;
   Ox86_ADC_instr.2;
   Ox86_ADCX_instr.2;
   Ox86_ADOX_instr.2;
   Ox86_MULX_instr.2;
   Ox86_SBB_instr.2;
   Ox86_NEG_instr.2;
   Ox86_INC_instr.2;
   Ox86_DEC_instr.2;
   Ox86_LZCNT_instr.2;
   Ox86_SETcc_instr.2;
   Ox86_BT_instr.2;
   Ox86_CLC_instr.2;
   Ox86_STC_instr.2;
   Ox86_LEA_instr.2;
   Ox86_TEST_instr.2;
   Ox86_CMP_instr.2;
   Ox86_AND_instr.2;
   Ox86_ANDN_instr.2;
   Ox86_OR_instr.2;
   Ox86_XOR_instr.2;
   Ox86_NOT_instr.2;
   Ox86_ROL_instr.2;
   Ox86_ROR_instr.2;
   Ox86_RCL_instr.2;
   Ox86_RCR_instr.2;
   Ox86_SHL_instr.2;
   Ox86_SHR_instr.2;
   Ox86_SAR_instr.2;
   Ox86_SAL_instr.2;
   Ox86_SHLD_instr.2;
   Ox86_SHRD_instr.2;
   Ox86_MOVD_instr.2;
   Ox86_VMOV_instr.2;
   Ox86_VPMOVSX_instr.2;
   Ox86_VPMOVZX_instr.2;
   Ox86_VPINSR_instr.2;
   Ox86_VEXTRACTI128_instr.2;
   Ox86_VMOVDQU_instr.2;
   Ox86_VPAND_instr.2;
   Ox86_VPANDN_instr.2;
   Ox86_VPOR_instr.2;
   Ox86_VPXOR_instr.2;
   Ox86_VPADD_instr.2;
   Ox86_VPSUB_instr.2;
   Ox86_VPMULL_instr.2;
   Ox86_VPMULU_instr.2;
   Ox86_VPMULH_instr.2;
   Ox86_VPMULHU_instr.2;
   Ox86_VPMULHRS_instr.2;
   Ox86_VPSLL_instr.2;
   Ox86_VPSRL_instr.2;
   Ox86_VPSRA_instr.2;
   Ox86_VPSLLV_instr.2;
   Ox86_VPSRLV_instr.2;
   Ox86_VPSLLDQ_instr.2;
   Ox86_VPSRLDQ_instr.2;
   Ox86_VPSHUFB_instr.2;
   Ox86_VPSHUFHW_instr.2;
   Ox86_VPSHUFLW_instr.2;
   Ox86_VPSHUFD_instr.2;
   Ox86_VSHUFPS_instr.2;
   Ox86_VPUNPCKH_instr.2;
   Ox86_VPUNPCKL_instr.2;
   Ox86_VPBLENDD_instr.2;
   Ox86_VPBROADCAST_instr.2;
   Ox86_VMOVSHDUP_instr.2;
   Ox86_VMOVSLDUP_instr.2;
   Ox86_VPALIGNR_instr.2;
   Ox86_VBROADCASTI128_instr.2;
   Ox86_VPERM2I128_instr.2;
   Ox86_VPERMD_instr.2;
   Ox86_VPERMQ_instr.2;
   Ox86_VINSERTI128_instr.2;
   Ox86_VPEXTR_instr.2;
   Ox86_PMOVMSKB_instr.2;
   Ox86_VPCMPEQ_instr.2;
   Ox86_VPCMPGT_instr.2;
   Ox86_VPMADDUBSW_instr.2;
   Ox86_VPMADDWD_instr.2;
   Ox86_VMOVLPD_instr.2;
   Ox86_VMOVHPD_instr.2;
   Ox86_RDTSC_instr.2;
   Ox86_RDTSCP_instr.2;
   Ox86_AESDEC_instr.2;            
   Ox86_VAESDEC_instr.2;         
   Ox86_AESDECLAST_instr.2;      
   Ox86_VAESDECLAST_instr.2;     
   Ox86_AESENC_instr.2;          
   Ox86_VAESENC_instr.2;         
   Ox86_AESENCLAST_instr.2;      
   Ox86_VAESENCLAST_instr.2;     
   Ox86_AESIMC_instr.2;          
   Ox86_VAESIMC_instr.2;         
   Ox86_AESKEYGENASSIST_instr.2; 
   Ox86_VAESKEYGENASSIST_instr.2
 ].
