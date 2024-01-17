(* -------------------------------------------------------------------- *)
require import AllCore FinType IntDiv SmtMap List.
require import StdOrder BitEncoding Bool Distr.
(*---*) import Ring.IntID IntOrder BS2Int.
require import JUtils JArray.

(* -------------------------------------------------------------------- *)
op undefined_flag : bool.

op rflags_of_mul (ov : bool) =
  let OF = ov in
  let CF = ov in
  let SF = undefined_flag in
  let PF = undefined_flag in
  let ZF = undefined_flag in
  (OF, CF, SF, PF, ZF).

op rflags_undefined = 
  let OF = undefined_flag in
  let CF = undefined_flag in
  let SF = undefined_flag in 
  let PF = undefined_flag in
  let ZF = undefined_flag in
  (OF, CF, SF, PF, ZF).

op flags_w (fs:bool * bool * bool * bool * bool) (w : 't) = 
  let (OF, CF, SF, PF, ZF) = fs in
  (OF, CF, SF, PF, ZF, w).

op flags_w2 (fs:bool * bool * bool * bool * bool) (w1 w2: 't) = 
  let (OF, CF, SF, PF, ZF) = fs in
  (OF, CF, SF, PF, ZF, w1, w2).

(* ------------------------------------------------------------------- *)

op _sLT (OF CF SF ZF :bool) =  OF <> SF.       (* CFC_L  OF CF SF ZF *)
op _uLT (OF CF SF ZF :bool) =  CF.             (* CFC_B  OF CF SF ZF. *)
op _sLE (OF CF SF ZF :bool) =  (OF<>SF) || ZF. (* CFC_LE OF CF SF ZF. *)
op _uLE (OF CF SF ZF :bool) =  CF || ZF.       (* CFC_BE OF CF SF ZF. *)
op _EQ  (OF CF SF ZF :bool) =  ZF.             (* CFC_E  OF CF SF ZF. *)
op _NEQ (OF CF SF ZF :bool) = !_EQ  OF CF SF ZF.
op _sGE (OF CF SF ZF :bool) = !_sLT OF CF SF ZF.
op _uGE (OF CF SF ZF :bool) = !_uLT OF CF SF ZF.
op _sGT (OF CF SF ZF :bool) = !_sLE OF CF SF ZF.
op _uGT (OF CF SF ZF :bool) = !_uLE OF CF SF ZF.

(* -------------------------------------------------------------------- *)

abstract theory BitWord.

op size : {int | 0 < size} as gt0_size.

clone FinType as Alphabet with
  type t    <- bool,
  op   enum <- [true; false],
  op   card <- 2.

clone include MonoArray with
  type elem <- bool,
  op dfl <- false,
  op size <- size
  rename "of_list"  as "bits2w"
         "to_list"  as "w2bits"
         "^tP$"     as "wordP"
         "sub"      as "bits"
  proof ge0_size by (apply ltzW; apply gt0_size).

(* -------------------------------------------------------------------- *)
abbrev modulus = 2 ^ size.

abbrev max_uint = modulus - 1.
lemma max_uintS: max_uint + 1 = modulus by done.

abbrev min_sint = - 2 ^ (size - 1).
abbrev max_sint =  2 ^ (size - 1) - 1.

lemma ge2_modulus : 2 <= modulus.
proof. rewrite powS_minus ?gt0_size; smt (gt0_size expr_gt0). qed.

lemma gt0_modulus : 0 < modulus.
proof. smt (ge2_modulus). qed.

lemma ge0_modulus : 0 <= modulus.
proof. smt (ge2_modulus). qed.

lemma max_size : max 0 size = size.
proof. by rewrite /max gt0_size. qed.

hint exact : ge0_size gt0_size gt0_modulus ge2_modulus ge0_modulus max_size.

(* --------------------------------------------------------------------- *)
(* Conversions with int                                                  *)

op of_int (x:int) : t =
  bits2w (int2bs size (x %% modulus))
axiomatized by of_intE.

op to_uint (w:t) =
  bs2int (w2bits w)
axiomatized by to_uintE.

op smod (i:int) =
  if 2^(size - 1) <= i then i - modulus
  else i.

op to_sint (w:t) : int = smod (to_uint w)
axiomatized by to_sintE.

abbrev zero = of_int 0.
abbrev one  = of_int 1.

lemma to_uint_cmp (x : t) : 0 <= to_uint x < modulus.
proof.
  by rewrite to_uintE bs2int_ge0 -(size_w2bits x) bs2int_le2Xs.
qed.

lemma to_sint_cmp (x : t) : min_sint <= to_sint x <= max_sint.
proof.
  smt(powS_minus gt0_size to_uint_cmp).
qed.

lemma of_uintK (x : int) : to_uint (of_int x) = x %% modulus.
proof.
  by rewrite to_uintE of_intE bits2wK 1:size_int2bs // int2bsK // modz_cmp.
qed.

lemma to_uintK : cancel to_uint of_int.
proof.
  move=> w; rewrite to_uintE of_intE.
  rewrite modz_small.
  + by rewrite bs2int_ge0 ger0_norm // -(size_w2bits w) bs2int_le2Xs.
  by rewrite -(size_w2bits w) bs2intK w2bitsK.
qed.

lemma to_uintK' (x: t) : of_int (to_uint x) = x.
proof. by apply to_uintK. qed.

(*hint simplify of_uintK@1. *)
hint simplify to_uintK'@0.

lemma of_sintK (x:int) :
   to_sint (of_int x) = smod (x %% modulus).
proof. by rewrite to_sintE of_uintK. qed.

lemma to_uint_mod (x : t) : to_uint x %% modulus = to_uint x.
proof. by rewrite modz_small // ger0_norm // to_uint_cmp. qed.

lemma of_int_mod (x : int) : of_int (x %% modulus) = of_int x.
proof. by apply/(can_inj _ _ to_uintK); rewrite !of_uintK modz_mod. qed.

lemma of_int_mod_red (x:int): !(0 <= x < modulus) => of_int x = of_int (x %% modulus).
proof. by rewrite of_int_mod. qed.

hint simplify of_int_mod_red.

lemma to_uint_small i : 0 <= i < modulus => to_uint (of_int i) = i.
proof. by move=> h; rewrite of_uintK modz_small;solve. qed.

lemma to_uint0 : to_uint (of_int 0) = 0 by rewrite of_uintK.
lemma to_uint1 : to_uint (of_int 1) = 1 by rewrite to_uint_small; smt (ge2_modulus).

hint simplify (to_uint0, to_uint1)@0.
hint simplify to_uint_small@1.

lemma word_modeqP (x y : t) :
  to_uint x %% modulus = to_uint y %% modulus => x = y.
proof.
move=> eq_mod; rewrite -(to_uintK x) -(to_uint_mod x).
by rewrite eq_mod to_uint_mod.
qed.

lemma to_uint_eq (x y:t) :  (x = y) <=> (to_uint x = to_uint y).
proof. by rewrite Core.inj_eq // (Core.can_inj _ _  to_uintK). qed.

(* -------------------------------------------------------------------- *)
(* Uniform distribution over word                                       *)
op all_words = map of_int (iota_ 0 modulus)
axiomatized by all_wordsE.

lemma all_wordsP x : x \in all_words.
proof. 
  rewrite all_wordsE mapP; exists (to_uint x).
  by rewrite mema_iota /= to_uint_cmp.
qed.

op dword = duniform all_words.

lemma dword_ll : is_lossless dword.
proof.
apply: duniform_ll; apply/negP=> eq0.
by have := all_wordsP witness; rewrite eq0.
qed.

lemma dword_uni : is_uniform dword.
proof. by apply duniform_uni. qed.

lemma dword_fu : is_full dword.
proof. by apply /duniform_fu/all_wordsP. qed.

lemma dword_funi : is_funiform dword.
proof. apply is_full_funiform;[apply dword_fu| apply dword_uni]. qed.

hint exact random : dword_ll dword_fu dword_funi.

(* -------------------------------------------------------------------- *)
op int_bit x i = (x%%modulus) %/ 2 ^ i %% 2 <> 0.

lemma of_intwE x i :
   (of_int x).[i] = (0 <= i < size /\ int_bit x i).
proof.
  rewrite of_intE; case (0 <= i < size) => /= hi; last by rewrite get_out.
  by rewrite get_bits2w // nth_mkseq.
qed.

lemma zerowE i: zero.[i] = false.
proof. by rewrite of_intwE /int_bit. qed.
hint simplify zerowE.

lemma of_int_powm1 p i :
  0 <= p =>
  (of_int (2^p - 1)).[i] = (0 <= i < size /\ i < p).
proof.
  case: (0 <= i < size) => [[h0i his] /= hp | hi]; last by rewrite get_out.
  have aux : forall p, 0 <= p <= size => (of_int (2 ^ p - 1)).[i] = (true /\ i < p).
  + move=> {p hp} p hp.
    rewrite of_intwE 1:// /int_bit /= (modz_small (2 ^ p - 1)).
    + smt (gt0_pow2 ler_weexpn2l).
    case (i < p) => hip /=.
    + have -> : p = ((p - i - 1) + 1) + i by ring.
      rewrite h0i his exprD_nneg // 1:/# divzMDl; 1: smt (gt0_pow2).
      by rewrite exprD_nneg 1:/# //= modzMDl divNz // gt0_pow2.
    by rewrite divz_small //; smt (gt0_pow2 ler_weexpn2l).
  case : (p <= size) => hps; 1: by apply aux.
  rewrite (_:i < p) 1:/# -of_int_mod.
  have -> : p = (p-size) + size by ring.
  rewrite exprD_nneg 1:/# 1://.
  by rewrite modzMDl -(modzMDl 1 (-1) modulus) /= of_int_mod aux 1:// his.
qed.

lemma get_to_uint w i : w.[i] = (0 <= i < size /\ to_uint w %/ 2 ^ i %% 2 <> 0).
proof.
  case : (0 <= i < size) => hi;last by rewrite get_out.
  rewrite -{1}(to_uintK w) of_intwE hi /int_bit (modz_small _ modulus) 2://.
  by apply bound_abs; apply to_uint_cmp.
qed.

lemma b2i_get w i : 0 <= i => b2i w.[i] = to_uint w %/ 2 ^ i %% 2.
proof.
  move=> hi;rewrite get_to_uint hi.
  case (i < size) => his //=; 1: smt (modz_cmp).
  rewrite divz_small //; apply bound_abs.
  smt (to_uint_cmp ler_weexpn2l ge0_size).
qed.

lemma bits_divmod w i j: 0 <= i => 0 <= j => bs2int (bits w i j) = ((to_uint w) %/ 2^i) %% 2^j.
proof.
  move => hi; rewrite /bits.
  elim /intind: j.
  + by rewrite mkseq0 bs2int_nil /=.
  move=> j hj hrec; rewrite mkseqS 1:// bs2int_rcons.
  rewrite size_mkseq ler_maxr 1:// /= hrec.
  have {2}->:= modz_pow_split (i+j+1) (i+j) (to_uint w) 2 _; 1: smt().
  have hij1 : 2 ^ (i + j + 1) = 2^(j+1) * 2^i.
  + by rewrite -exprD_nneg 1:/# 1://;congr;ring.
  have hij : 2 ^ (i + j) = 2^j * 2^i.
  + by rewrite -exprD_nneg 1:/# 1://;congr;ring.
  have h2i0 : 2 ^ i <> 0 by smt (gt0_pow2).
  rewrite -addzA {2}hij1 -mulzA divzMDl 1://.
  rewrite {2}hij -mulzA divzMDl 1://.
  rewrite modzMDl !modz_pow2_div; 1,2:smt().
  have -> : i + j + 1 - (i + j) = 1 by ring.
  have -> : i + j - i = j by ring.
  rewrite (exprD_nneg 2 j 1) 1,2:// pow2_1 (modz_small _ (2^j * 2)).
  + apply bound_abs; split => [|?]; 1: smt (modz_cmp to_uint_cmp gt0_pow2).
    by rewrite -hrec; smt (modz_cmp to_uint_cmp gt0_pow2).
  by rewrite addzC mulzC b2i_get 1:/#.
qed.

lemma bitsE w k len : bits w k len = mkseq (fun (i:int) => w.[k+i]) len.
proof. done. qed.

lemma to_uintRL (w:t) (x:int) : to_uint w = x %% 2^size => w = of_int x.
proof.
  by move=> h;rewrite -of_int_mod; apply: (canRL _ _ _ _ to_uintK).
qed.

lemma to_uint_bits w : to_uint w = bs2int (bits w 0 size).
proof. by rewrite to_uintE /w2bits /bits /=. qed.

(* -------------------------------------------------------------------- *)
op zerow = zero.

op onew  = of_int (modulus - 1)
axiomatized by oneE.

op (+^) : t -> t -> t = map2 (^^)
axiomatized by xorE.

op andw : t -> t -> t = map2 (/\)
axiomatized by andE.

op oppw (w : t): t = w.

op invw : t -> t = map ([!])
axiomatized by invE.

op orw : t -> t -> t = map2 (\/)
axiomatized by orE.

(* -------------------------------------------------------------------- *)

lemma zerowiE i: zerow.[i] = false.
proof. apply zerowE. qed.

lemma onewE i: onew.[i] = (0 <= i < size).
proof.
  rewrite oneE; case (0 <= i < size) => hi; 2:by rewrite get_out.
  by rewrite of_int_powm1 //= 1:/# hi.
qed.

lemma xorwE w1 w2 i: (w1 +^ w2).[i] = w1.[i] ^^ w2.[i].
proof.
  by rewrite xorE; case (0 <= i < size) => hi;[ rewrite map2iE | rewrite !get_out].
qed.

lemma andwE (w1 w2:t) i: (andw w1 w2).[i] = (w1.[i] /\ w2.[i]).
proof.
  by rewrite andE; case (0 <= i < size) => hi;[ rewrite map2iE | rewrite !get_out].
qed.

lemma orwE (w1 w2:t) i: (orw w1 w2).[i] = (w1.[i] \/ w2.[i]).
proof.
  by rewrite orE; case (0 <= i < size) => hi;[ rewrite map2iE | rewrite !get_out].
qed.

lemma invwE (w:t) i:
  (invw w).[i] = (0 <= i < size /\ !w.[i]).
proof. by rewrite invE mapE initE;case (0 <= i < _). qed.

lemma oppwE (w:t) i: (oppw w).[i] = w.[i].
proof. by []. qed.

hint rewrite bwordE : zerowE zerowiE onewE xorwE andwE invwE.
hint simplify (zerowE, zerowiE, onewE, xorwE, andwE, invwE, orwE).

(* -------------------------------------------------------------------- *)
lemma onew_neq0: onew <> zerow.
proof.
  apply/negP=> /wordP/(_ 0) /=.
  by rewrite negb_imply neqF.
qed.

lemma xorw0: right_id zero (+^).
proof. by move=> w; apply/wordP=> i _. qed.

lemma xorwA: associative (+^).
proof. by move=> w1 w2 w3; apply/wordP=> i _; rewrite !bwordE xorA. qed.

lemma xorwC: commutative (+^).
proof. by move=> w1 w2; apply/wordP=> i _; rewrite !bwordE xorC. qed.

lemma xorwK: forall x, x +^ x = zero.
proof. by move=> w; apply/wordP=> i _; rewrite !bwordE. qed.

lemma andw1: right_id onew andw.
proof. by move=> w; apply/wordP=> i h; rewrite !bwordE h. qed.

lemma andwA: associative andw.
proof. by move=> w1 w2 w3; apply/wordP=> i h; rewrite !bwordE andbA. qed.

lemma andwC: commutative andw.
proof. by move=> w1 w2; apply/wordP=> i h; rewrite !bwordE andbC. qed.

lemma andwDl: left_distributive andw (+^).
proof. move=> w1 w2 w3; apply/wordP=> i h; rewrite !bwordE /#. qed.

lemma andwK: idempotent andw.
proof. by move=> x; apply/wordP=> i h; rewrite !bwordE andbb. qed.

(* -------------------------------------------------------------------- *)
instance bring with t
  op rzero = zerow
  op rone  = onew
  op add   = (+^)
  op mul   = andw
  op opp   = oppw

  proof oner_neq0 by apply/onew_neq0
  proof addr0     by apply/xorw0
  proof addrA     by (move=> w1 w2 w3; rewrite xorwA)
  proof addrC     by apply/xorwC
  proof addrK     by apply/xorwK
  proof mulr1     by apply andw1
  proof mulrA     by (move=> w1 w2 w3; rewrite andwA)
  proof mulrC     by apply/andwC
  proof mulrDl    by apply/andwDl
  proof mulrK     by apply/andwK
  proof oppr_id   by trivial.

pred unitw (w:t) = w = onew.
op iandw (w:t) = if w = onew then onew else w.

clone Ring.ComRing as WRing with
   type t <- t,
   op zeror <- zero,
   op ( + ) <- (+^),
   op [ - ] <- oppw,
   op oner  <- onew,
   op ( * ) <- andw,
   op invr  <- iandw,
   pred unit <- unitw
proof *.
realize addrA.     proof. apply xorwA. qed.
realize addrC.     proof. apply xorwC. qed.
realize add0r.     proof. move=> ?;ring. qed.
realize addNr.     proof. move=> ?;ring. qed.
realize oner_neq0. proof. apply onew_neq0. qed.
realize mulrA.     proof. apply andwA. qed.
realize mulrC.     proof. apply andwC. qed.
realize mul1r.     proof. move=> ?;ring. qed.
realize mulrDl.    proof. apply andwDl. qed.
realize mulVr.     proof. move=> ?;rewrite /unitw /iandw => -> /=;ring. qed.
realize unitout.   proof. by move=> x;rewrite /unitw /iandw => ->. qed.

realize unitP.
proof.
move=> x y; rewrite /unitw !wordP => + i Hi -/(_ i Hi).
by rewrite andwE onewE Hi /#.
qed.

lemma xor0w w : of_int 0 +^ w = w.
proof. by apply WRing.add0r. qed.

lemma xorw0_s w : w +^ of_int 0 = w.
proof. by apply WRing.addr0. qed.

lemma xorw1 w : w +^ onew = invw w.
proof. by apply wordP => i hi /=; case (0 <= i < size). qed.

lemma xor1w w : onew +^ w = invw w.
proof. by apply wordP => i hi /=; case (0 <= i < size). qed.

lemma and0w w : andw (of_int 0) w = of_int 0.
proof. by apply WRing.mul0r. qed.

lemma andw0 w : andw w (of_int 0) = of_int 0.
proof. by apply WRing.mulr0. qed.

lemma and1w w : andw onew w = w.
proof. by apply WRing.mul1r. qed.

lemma andw1_s w : andw w onew = w.
proof. by apply WRing.mulr1. qed.

lemma orw0 w : orw w zero = w.
proof. by apply wordP => i hi. qed.

lemma or0w w : orw zero w = w.
proof. by apply wordP => i hi. qed.

lemma orw1 w : orw w onew = onew.
proof. by apply wordP => i hi /=; case (0 <= i < size). qed.

lemma or1w w : orw onew w = onew.
proof. by apply wordP => i hi /=; case (0 <= i < size). qed.

lemma orwK w : orw w w = w.
proof. by apply wordP => i hi /=; case (w.[i]). qed.

lemma xorwK_s w1 w2 : w1 = w2 => (w1 +^ w2) = zero.
proof. move=> ->;apply xorwK. qed.

lemma andwK_s w1 w2 : w1 = w2 => andw w1 w2 = w1.
proof. move=> ->;apply andwK. qed.

lemma orwK_s w1 w2 : w1 = w2 => orw w1 w2 = w1.
proof. move=> ->;apply orwK. qed.

lemma andw_invw w: andw w (invw w) = zerow.
proof. by rewrite -xorw1; ring. qed.

lemma nosmt orw_xorw w1 w2: orw w1 w2 = w1 +^ w2 +^ (andw w1 w2).
proof.
apply wordP => i Hi.
rewrite orE !xorE andE !map2iE //.
by case: w1.[i]; case: w2.[i].
qed.

lemma nosmt andw_orwDl: left_distributive andw orw.
proof.
by move=> x y z; rewrite !orw_xorw; ring.
qed.

lemma nosmt andw_orwDr: right_distributive andw orw.
proof.
by move=> x y z; rewrite !orw_xorw; ring.
qed.

lemma nosmt orw_andwDl: left_distributive orw andw.
proof.
by move=> x y z; rewrite !orw_xorw; ring.
qed.

lemma nosmt orw_andwDr: right_distributive orw andw.
proof.
by move=> x y z; rewrite !orw_xorw; ring.
qed.

lemma orwC x y: orw x y = orw y x.
proof. by rewrite orw_xorw andwC (xorwC x) -orw_xorw. qed.

lemma xorw_invw w: w +^ (invw w) = onew.
proof.
apply wordP => i Hi.
rewrite xorE !map2iE // onewE invwE !Hi /=.
by case: w.[i].
qed.

lemma orw_invw w: orw w (invw w) = onew.
proof. by rewrite orw_xorw andw_invw -xorwA xorw0_s xorw_invw. qed.

hint simplify (xor0w, xorw0_s, xorw1, xor1w,
               and0w, andw0, and1w, andw1_s,
               or0w, orw0, orw1, or1w,
               xorwK_s, andwK_s, orwK_s).

(* --------------------------------------------------------------------- *)
(* Arimethic operations                                                  *)

op ulift1 (f : int -> int) (w : t) =
  of_int (f (to_uint w)).

op ulift2 (f : int -> int -> int) (w1 w2 : t) =
  of_int (f (to_uint w1) (to_uint w2)).

op slift2 (f : int -> int -> int) (w1 w2 : t) =
  of_int (f (to_uint w1) (to_uint w2)).

op ( + ) = ulift2 Int.( + ) axiomatized by addE.
op ([-]) = ulift1 Int.([-]) axiomatized by oppE.
op ( * ) = ulift2 Int.( * ) axiomatized by mulE.

op (\udiv) = ulift2 IntDiv.( %/) axiomatized by udivE.
op (\umod) = ulift2 IntDiv.( %%) axiomatized by umodE.

(* TODO check this *)
op (\sdiv) = slift2 IntDiv.( %/) axiomatized by sdivE.
op (\smod) = slift2 IntDiv.( %%) axiomatized by smodE.

(* --------------------------------------------------------------------- *)
(* Comparisons                                                           *)

op (\ule) (x y : t) = (to_uint x) <= (to_uint y) axiomatized by uleE.
op (\ult) (x y : t) = (to_uint x) <  (to_uint y) axiomatized by ultE.

op (\sle) (x y : t) = (to_sint x) <= (to_sint y) axiomatized by sleE.
op (\slt) (x y : t) = (to_sint x) <  (to_sint y) axiomatized by sltE.

lemma ult_of_int x y :
   (of_int x \ult of_int y) = (x %% modulus < y %% modulus).
proof. by rewrite ultE /= !of_uintK. qed.

lemma ule_of_int x y :
   (of_int x \ule of_int y) = (x %% modulus <= y %% modulus).
proof. by rewrite uleE /= !of_uintK. qed.

lemma uleNgt x y : x \ule y <=> ! y \ult x.
proof. by rewrite ultE uleE lerNgt. qed.

lemma ultNge x y: x \ult y <=> ! y \ule x.
proof. by rewrite ultE uleE ltzNge. qed.

lemma ult_of_int_true x y :
   (x %% modulus < y %% modulus) => (of_int x \ult of_int y) = true.
proof. by rewrite ult_of_int => ->. qed.

lemma ult_of_int_false x y :
   !(x %% modulus < y %% modulus) => (of_int x \ult of_int y) = false.
proof. by rewrite ult_of_int => ->. qed.

lemma ule_of_int_true x y :
   (x %% modulus <= y %% modulus) => (of_int x \ule of_int y) = true.
proof. by rewrite ule_of_int => ->. qed.

lemma ule_of_int_false x y :
   !(x %% modulus <= y %% modulus) => (of_int x \ule of_int y) = false.
proof. by rewrite ule_of_int => ->. qed.

hint simplify (ult_of_int_true, ult_of_int_false, ule_of_int_true, ule_of_int_false).

(* --------------------------------------------------------------------- *)
(* ComRing                                                               *)

op is_inverse (w wi: t) = wi * w = of_int 1.
op unit (w:t) = exists wi, is_inverse w wi.
op invr (w:t) = Logic.choiceb (is_inverse w) w.

lemma of_intN (x : int) : of_int (-x) = - of_int x.
proof.
rewrite oppE /ulift1 /=; apply/word_modeqP=> /=.
by rewrite !of_uintK !modz_mod modzNm.
qed.

lemma to_uintN (x : t) : to_uint (-x) = (- to_uint x) %% modulus.
proof. by rewrite oppE /ulift1 of_uintK. qed.

lemma of_intD (x y : int) : of_int (x + y) = of_int x + of_int y.
proof.
rewrite addE /ulift2 /=; apply/word_modeqP=> /=.
by rewrite !of_uintK !modz_mod !(modzDml, modzDmr).
qed.

lemma to_uintD (x y : t) : to_uint (x + y) = (to_uint x + to_uint y) %% modulus.
proof. by rewrite addE /ulift2 of_uintK. qed.

lemma of_intM (x y : int) : of_int x * of_int y = of_int (x * y).
proof.
rewrite mulE /ulift2 /=; apply/word_modeqP=> /=.
by rewrite !of_uintK !modz_mod !(modzMml, modzMmr).
qed.

lemma to_uintM (x y : t) : to_uint (x * y) = (to_uint x * to_uint y) %% modulus.
proof. by rewrite mulE /ulift2 !of_uintK. qed.

lemma to_uintD_small (x y : t) : to_uint x + to_uint y < modulus =>
  to_uint (x + y) = to_uint x + to_uint y.
proof.
  move=> h;rewrite to_uintD modz_small 2://; smt (to_uint_cmp).
qed.

lemma to_uintM_small (x y : t) : to_uint x * to_uint y < modulus =>
  to_uint (x * y) = (to_uint x * to_uint y).
proof.
  move=> h;rewrite to_uintM modz_small 2://; smt (to_uint_cmp).
qed.

clone export Ring.ComRing as WRingA with
   type t <- t,
   op zeror <- of_int 0,
   op ( + ) <- BitWord.( + ),
   op [ - ] <- BitWord.([-]),
   op oner  <- of_int 1,
   op ( * ) <- BitWord.( * ),
   op invr  <- invr,
   pred unit  <- BitWord.unit proof *.

realize addrA.
proof.
  move=> x y z; rewrite addE /ulift2 !to_uintD -of_int_mod modzDmr.
  by rewrite -(of_int_mod (_ + to_uint z)) modzDml addrA.
qed.

realize addrC.
proof. by move=> x y; rewrite !addE /ulift2 addzC. qed.

realize add0r.
proof. by move=> x; rewrite addE /ulift2; cbv delta. qed.

realize addNr.
proof.
  move=> x; rewrite addE oppE /ulift2 /ulift1 of_uintK.
  by rewrite -of_int_mod modzDml addNz.
qed.

realize oner_neq0.
proof.
  apply /negP => heq.
  have := of_uintK 1; rewrite heq of_uintK mod0z.
  rewrite modz_small //;smt (ge2_modulus).
qed.

realize mulrA.
 move=> x y z; rewrite mulE /ulift2 !to_uintM -of_int_mod modzMmr.
  by rewrite -(of_int_mod (_ * to_uint z)) modzMml mulrA.
qed.

realize mulrC.
proof. by move=> x y; rewrite !mulE /ulift2 mulzC. qed.

realize mul1r.
proof. by move=> x; rewrite mulE /ulift2 to_uint1. qed.

realize mulrDl.
proof.
  move=> x y z; rewrite !addE !mulE /ulift2.
  rewrite !of_uintK -of_int_mod modzMml eq_sym.
  by rewrite -of_int_mod modzDml modzDmr mulrDl.
qed.

realize mulVr.
proof. by move=> x /choicebP /= ->. qed.

realize unitP.
proof. by move=> w wi hinv;exists wi. qed.

realize unitout.
proof. by move=> x /negb_exists /=; apply choiceb_dfl. qed.

abbrev (^) = WRingA.exp.

lemma ofintS (n : int) : 0 <= n => of_int (n + 1) = of_int 1 + of_int n.
proof. by rewrite of_intD addrC. qed.

lemma to_uintB (x y: t) : y \ule x => to_uint (x - y) = to_uint x - to_uint y.
proof.
  rewrite uleE=> hle.
  rewrite to_uintD to_uintN modzDmr modz_small //; smt (to_uint_cmp).
qed.

(* Add simplification rule for rewriting *)
(* FIXME add direction for hint simplify *)
lemma of_intN' (x : int) : - of_int x = of_int (-x).
proof. by rewrite of_intN. qed.

lemma of_intS (x y : int) : of_int (x - y) = of_int x - of_int y.
proof. by rewrite of_intD of_intN. qed.

lemma of_intS' (x y : int) : of_int x - of_int y = of_int (x - y).
proof. by rewrite of_intS. qed.

lemma of_intD' (x y : int) : of_int x + of_int y = of_int (x + y).
proof. by rewrite of_intD. qed.

lemma of_intM' (x y : int) : of_int x * of_int y = of_int (x * y).
proof. by rewrite of_intM. qed.

hint simplify (of_intS', of_intM')@0.
hint simplify (of_intD')@1.

lemma addr0_s w : w + of_int 0 = w.
proof. by apply addr0. qed.

lemma add0r_s w : of_int 0 + w = w.
proof. by apply add0r. qed.

lemma mulr1_s w : w * of_int 1 = w.
proof. by apply mulr1. qed.

lemma mul1r_s w : of_int 1 * w = w.
proof. by apply mul1r. qed.

lemma mulr0_s w : w * of_int 0 = of_int 0.
proof. by apply mulr0. qed.

lemma mul0r_s w : of_int 0 * w = of_int 0.
proof. by apply mul0r. qed.

lemma addA_ofint w i j : w + of_int i + of_int j = w + of_int (i + j).
proof. by rewrite -addrA. qed.

lemma addS_ofint w i j : w + of_int i - of_int j = w + of_int (i - j).
proof. by rewrite -addrA -of_intS. qed.

hint simplify (addr0_s, add0r_s, mul1r_s, mulr1_s, mul0r_s, mulr0_s, addA_ofint).



(* --------------------------------------------------------------------- *)
(* Ring tactic                                                           *)

op zerow_ring = of_int 0.
op onew_ring  = of_int 1.

instance ring with t
  op rzero = BitWord.zerow_ring
  op rone  = BitWord.onew_ring
  op add   = BitWord.( + )
  op opp   = BitWord.([-])
  op mul   = BitWord.( * )
  op expr  = WRingA.exp
  op ofint = BitWord.of_int

  proof oner_neq0 by apply oner_neq0
  proof addr0     by apply addr0
  proof addrA     by apply addrA
  proof addrC     by apply addrC
  proof addrN     by apply addrN
  proof mulr1     by apply mulr1
  proof mulrA     by apply mulrA
  proof mulrC     by apply mulrC
  proof mulrDl    by apply mulrDl
  proof expr0     by apply expr0
  proof exprS     by apply exprS
  proof ofint0    by done
  proof ofint1    by done
  proof ofintS    by apply ofintS
  proof ofintN    by apply of_intN.

(* --------------------------------------------------------------------- *)
(* Exact arithmetic operations                                           *)
(*
op subc : t -> t -> bool -> bool * t.
op addc : t -> t -> bool -> bool * t.
op mulu : t -> t -> t * t.
*)

op borrow_sub x y b = to_uint x < to_uint y + b2i b.

op subc (x y:t) (b: bool): bool * t = (borrow_sub x y b, x-(y+of_int (b2i b)))
 axiomatized by subcE.

lemma subcP x y c:
 let (c',z) = subc x y c
 in to_uint z - modulus * b2i c' = to_uint x - (to_uint y + b2i c).
proof.
rewrite subcE /borrow_sub /=.
case: (to_uint y + b2i c = modulus) => H.
 rewrite to_uintD.
 have -> /=: to_uint (- (y + of_int (b2i c))) = 0.
  rewrite to_uintN to_uintD of_uintK (modz_small (b2i c)).
   by apply bound_abs; smt(ge2_modulus).
  by rewrite H modzz /=.
 rewrite H modz_small.
  by apply bound_abs; apply to_uint_cmp.
 have ->: to_uint x < modulus by smt(to_uint_cmp).
 smt().
case: (to_uint x < to_uint y + b2i c) => ?/=.
 have E: to_uint y + b2i c = to_uint (y + of_int (b2i c)).
  rewrite to_uintD_small.
   rewrite !of_uintK modz_small; first by  apply bound_abs; smt(ge2_modulus).
   by case: c => /=?; smt(to_uint_cmp).
  by rewrite of_uintK modz_small //; apply bound_abs; smt(ge2_modulus).
 rewrite E b2i1 /= eqr_sub.
 have ->: x - (y + of_int (b2i c)) = -((y + of_int (b2i c)) - x) by ring.
 rewrite to_uintN -modzDl modz_small.
  have ?: 0 < to_uint (y + of_int (b2i c) - x) <= `|modulus|.
   rewrite to_uintB; first by rewrite uleE -E; smt().
   rewrite -E; smt(to_uint_cmp).
  smt(to_uint_cmp).
 rewrite to_uintB; first by rewrite uleE -E; smt().
 smt(to_uint_cmp).
rewrite b2i0 /= to_uintB.
 rewrite uleE to_uintD_small.
  by rewrite of_uintK modz_small; smt(to_uint_cmp ge2_modulus).
 rewrite of_uintK modz_small; first smt(ge2_modulus).
 smt(ge2_modulus to_uint_cmp).
by rewrite to_uintD of_uintK !modz_small; smt(ge2_modulus to_uint_cmp).
qed.

abbrev subc_borrow x y c = (subc x y c).`1.

op carry_add x y c = modulus <= to_uint x + to_uint y + b2i c.

lemma carry_addC x y c: carry_add x y c = carry_add y x c.
proof. by rewrite /carry_add (addzC (to_uint x)). qed.

op addc (x y: t) (c: bool) : bool * t = (carry_add x y c, x+y+of_int (b2i c))
 axiomatized by addcE.

lemma addcP x y c:
 let (c',z) = addc x y c
 in to_uint z + modulus * b2i c' = to_uint x + to_uint y + b2i c.
proof.
rewrite addcE !addE /ulift2 /= !of_uintK /= modzDmr modzDml /carry_add.
have /= ?: to_uint x + to_uint y + b2i c < 2*modulus.
 by move: (to_uint_cmp x) (to_uint_cmp y); smt().
case: (modulus <= to_uint x + to_uint y + b2i c) => /= ?.
 have {1}->: to_uint x + to_uint y + b2i c = to_uint x + to_uint y + b2i c - modulus + modulus
  by ring.
 rewrite b2i1 modzDr modz_small.
  by apply bound_abs; smt(to_uint_cmp bound_abs).
 by ring.
by rewrite modz_small; smt(to_uint_cmp bound_abs).
qed.

abbrev addc_carry x y c = (addc x y c).`1.

op mulhi (x y: t) : t =
 of_int ((to_uint x * to_uint y) %/ modulus).

lemma mulhiP (x y: t):
 to_uint (x*y) + modulus * to_uint (mulhi x y) = to_uint x * to_uint y.
proof.
have [??] := (to_uint_cmp x).
have [??] := (to_uint_cmp y).
rewrite to_uintM to_uint_small.
 apply divz_cmp; first smt().
 split; first smt().
 by move=> _; apply ltr_pmul.
by rewrite {3}(divz_eq (to_uint x * to_uint y) modulus) /#.
qed.

lemma mulhi0 (x y: t):
 to_uint x* to_uint y < modulus => to_uint (mulhi x y) = 0.
proof.
move=> ?; rewrite /mulhi divz_small //; apply bound_abs.
split=> //; smt (to_uint_cmp).
qed.

op mulu (x y: t): t * t = (mulhi x y, x*y) axiomatized by muluE.

(* --------------------------------------------------------------------- *)
(* Bitwize operations                                                    *)

abbrev (`&`) = andw.
abbrev (`|`) = orw.
abbrev (`^`) = (+^).

op msb (b: t): bool = 2^(size - 1) <= (to_uint b).

op lsb (w: t): bool = w.[0].

op (`>>>`) (x : t) (i : int) =
  init (fun j => x.[j + i])
axiomatized by wlsrE.

op (`<<<`) (x : t) (i : int) =
  init (fun j => x.[j - i])
axiomatized by wlslE.

op sar (x:t) (i:int) =
  init (fun j => x.[min (size- 1) (j + i)])
axiomatized by sarE.

lemma shlwE w k i : (w `<<<` k).[i] = (0 <= i < size && w.[i - k]).
proof. by rewrite wlslE initE. qed.

lemma shrwE w k i : (w `>>>` k).[i] = (0 <= i < size && w.[i + k]).
proof. by rewrite wlsrE initE. qed.
hint simplify (shrwE, shlwE).

lemma int_bitMP i j k : 0 <= k => 0 <= j < size =>
  int_bit (i * 2 ^ k) j = (0 <= j - k < size /\ int_bit i (j - k)).
proof.
  move=> hk [h0j hjs];rewrite /int_bit modz_pow2_div 1:/# modz_dvd.
  + by have /= := dvdz_exp2l 2 1; apply => /#.
  case: (0 <= j - k < size) => [ [hjk1 hjk2] | hjk]  /=;last first.
  + have hlt : (j < k) by smt().
    have ->: k = (k-j-1) + 1 + j by ring.
    rewrite exprD_nneg 1:/# 1:// -mulzA mulzK; 1: smt (gt0_pow2).
    by rewrite exprD_nneg 1:/# //= -mulzA modzMl.
  rewrite (modz_pow2_div size) 1:/# modz_dvd.
  + by have /= := dvdz_exp2l 2 1; apply => /#.
  have {1}-> : j = (j - k) + k by ring.
  by rewrite exprD_nneg 1,2:// divzMpr 1:gt0_pow2.
qed.

lemma int_bitDP i j k : 0 <= i < modulus => 0 <= k => 0 <= j < size =>
  int_bit (i %/ 2 ^ k) j = (0 <= j + k < size /\ int_bit i (j + k)).
proof.
  move=> hi hk [h0j hjs];rewrite /int_bit.
  rewrite !(modz_small _ modulus); 1,2: apply bound_abs; 2:done.
  + by apply divz_cmp; [apply gt0_pow2 | smt (gt0_pow2)].
  case: (0 <= j + k < size) => hjk.
  + have {1}->:= divz_eq i (2^(j+k)).
    have {1}->:= divz_eq (i %% 2 ^ (j + k)) (2^k).
    pose id := i %/ 2 ^ (j + k). pose im := i %% 2 ^ (j + k).
    have -> : id * 2 ^ (j + k) + (im %/ 2 ^ k * 2 ^ k + im %% 2 ^ k) =
           (id * 2^j + im %/ 2 ^ k) * 2^k + im %% 2 ^ k.
    + by rewrite exprD_nneg 1,2://;ring.
    rewrite divzMDl. smt (gt0_pow2).
    rewrite (divz_small (im %% 2 ^ k) (2 ^ k)).
    + apply bound_abs;apply modz_cmp;apply gt0_pow2.
    rewrite /= divzMDl. smt (gt0_pow2).
    rewrite (divz_small (im %/ 2 ^ k) (2 ^ j)) 2://.
    apply bound_abs; apply divz_cmp; 1:by apply gt0_pow2.
    by rewrite -exprD_nneg 1,2://;apply modz_cmp;apply gt0_pow2.
  rewrite /= (divz_small (i %/ 2 ^ k) (2 ^ j)) 2://.
  apply bound_abs;apply divz_cmp; 1: by apply gt0_pow2.
  rewrite -exprD_nneg 1,2://;smt (ler_weexpn2l).
qed.

lemma shlMP i k : 0 <= k => (of_int i `<<<` k) = of_int (i * 2^k).
proof.
  by move=> hk;apply wordP => j hj; rewrite shlwE !of_intwE hj /= -int_bitMP.
qed.

lemma shrDP i k : 0 <= k => (of_int i `>>>` k) = of_int (i %% modulus %/ 2^k).
proof.
  move=> hk;rewrite -(of_int_mod i).
  apply wordP => j hj; rewrite shrwE !of_intwE hj /= -int_bitDP //.
  by apply modz_cmp.
qed.

lemma to_uint_shl (w:t) i :
  0 <= i => to_uint (w `<<<` i) = (to_uint w * 2^ i) %% modulus.
proof.
  by move=> hi; rewrite -{1}(to_uintK w) shlMP 1:// of_uintK.
qed.

lemma to_uint_shr (w:t) i :
  0 <= i => to_uint (w `>>>` i) = to_uint w %/ 2^ i.
proof.
  move=> hi;rewrite -{1}(to_uintK w) shrDP 1:// of_uintK.
  rewrite (modz_small (to_uint w)).
  + by apply bound_abs; apply to_uint_cmp.
  rewrite modz_small 2://.
  apply bound_abs; apply divz_cmp; [apply gt0_pow2 | ].
  smt (to_uint_cmp gt0_pow2).
qed.

lemma shrw_shlw w i : w `>>>` i = w `<<<` (-i).
proof. by apply wordP => k hk /=. qed.

lemma shrw_add w i j : 0 <= i => 0 <= j => w `>>>` i `>>>` j = w `>>>` (i + j).
proof.
  move=> hi hj; apply wordP => k hk /=;rewrite hk /=.
  case : (0 <= k + j < size) => hkj /=; 1:congr;ring.
  by rewrite get_out 1:/#.
qed.

lemma shrw_out w i : size <= i => w `>>>` i = zero.
proof.
  by move=> hi;apply wordP => k hk/=; rewrite get_out 1:/#.
qed.
hint simplify (shrw_add, shrw_out).

lemma shlw_add w i j : 0 <= i => 0 <= j => w `<<<` i `<<<` j = w `<<<` (i + j).
proof.
  move=> hi hj; apply wordP => k hk /=;rewrite hk /=.
  case : (0 <= k - j < size) => hkj /=; 1:congr;ring.
  by rewrite get_out 1:/#.
qed.

lemma shlw_out w i : size <= i => w `<<<` i = zero.
proof.
  by move=> hi;apply wordP => k hk/=; rewrite get_out 1:/#.
qed.
hint simplify (shlw_add, shlw_out).

lemma shrw_map2 f w1 w2 i : f false false = false =>
   (map2 f) (w1 `>>>` i) (w2 `>>>` i) = (map2 f w1 w2) `>>>` i.
proof.
  move=> hf;apply wordP => k hk.
  rewrite map2iE // !shrwE hk.
  case: (0 <= k + i < size) => hki; 1: by rewrite map2iE.
  by rewrite !get_out.
qed.

lemma shlw_map2 f w1 w2 i : f false false = false =>
   (map2 f) (w1 `<<<` i) (w2 `<<<` i) = (map2 f w1 w2) `<<<` i.
proof.
  move=> hf;apply wordP => k hk.
  rewrite map2iE // !shlwE hk.
  case: (0 <= k - i < size) => hki; 1: by rewrite map2iE.
  by rewrite !get_out.
qed.

lemma shrw_and w1 w2 i : (w1 `>>>` i) `&` (w2 `>>>` i) = (w1 `&` w2) `>>>` i.
proof. by rewrite andE shrw_map2. qed.

lemma shrw_xor w1 w2 i : (w1 `>>>` i) `^` (w2 `>>>` i) = (w1 `^` w2) `>>>` i.
proof. by rewrite xorE shrw_map2. qed.

lemma shrw_or w1 w2 i : (w1 `>>>` i) `|` (w2 `>>>` i) = (w1 `|` w2) `>>>` i.
proof. by rewrite orE shrw_map2. qed.

lemma shlw_and w1 w2 i : (w1 `<<<` i) `&` (w2 `<<<` i) = (w1 `&` w2) `<<<` i.
proof. by rewrite andE shlw_map2. qed.

lemma shlw_xor w1 w2 i : (w1 `<<<` i) `^` (w2 `<<<` i) = (w1 `^` w2) `<<<` i.
proof. by rewrite xorE shlw_map2. qed.

lemma shlw_or w1 w2 i : (w1 `<<<` i) `|` (w2 `<<<` i) = (w1 `|` w2) `<<<` i.
proof. by rewrite orE shlw_map2. qed.

hint simplify (shrw_and, shrw_xor, shrw_or, shlw_and, shlw_xor, shlw_or).

op ror (x : t) (i : int) =
  init (fun j => x.[(j + i) %% size])
axiomatized by rorE.

op rol (x : t) (i : int) =
  init (fun j => x.[(j - i) %% size])
axiomatized by rolE.

abbrev (`|>>>|`) = ror.
abbrev (`|<<<|`) = rol.

lemma rorwE w k i :
  (w `|>>>|` k).[i] = if (0 <= i < size) then w.[(i+k) %% size] else false.
proof. by rewrite rorE initE. qed.

lemma rolwE w k i :
  (w `|<<<|` k).[i] = if (0 <= i < size) then w.[(i-k) %% size] else false.
proof. by rewrite rolE initE. qed.

hint simplify (rorwE, rolwE).

lemma rol_xor w i : 0 <= i < size =>
  w `|<<<|` i = (w `<<<` i) `^` (w `>>>` (size - i)).
proof.
  move=> hi; apply wordP => k hk /=.
  rewrite hk /=.
  case (0 <= k - i < size) => hki.
  + rewrite modz_small; 1: by apply bound_abs.
    by rewrite (get_out _ (k + (size - i))) 1:/#.
  rewrite modz_sub_carry // 1:/# (get_out _ _ hki) /=.
  by congr;ring.
qed.

lemma rol_xor_simplify w1 w2 i si:
   w1 = w2 => si = size - i => 0 <= i < size =>
   (w1 `<<<` i) `^` (w2 `>>>` si) = w1 `|<<<|` i.
proof. by move=> 2!-> hi;rewrite rol_xor. qed.

(* --------------------------------------------------------------------- *)
(* Like between bitwize operations and arithmetic operations             *)

lemma and_mod k w :
  0 <= k =>
    w `&` of_int (2^k - 1) = of_int (to_uint w %% 2^k).
proof.
  move=> hk;apply wordP => i hi /=.
  rewrite of_int_powm1 1:// of_intwE hi /= /int_bit.
  rewrite (modz_small _ modulus).
  + apply bound_abs; smt (le_modz modz_cmp to_uint_cmp gt0_pow2).
  case (i < k) => hik /=.
  + rewrite modz_pow2_div 1:/# modz_dvd.
    + by have /= := dvdz_exp2l 2 1; apply => /#.
    by rewrite get_to_uint hi.
  rewrite divz_small 2://; smt (gt0_pow2 modz_cmp ler_weexpn2l).
qed.

lemma to_uint_and_mod k w :
  0 <= k =>
    to_uint (w `&` of_int (2^k - 1)) = to_uint w %% 2^k.
proof.
  move=> hk ; rewrite and_mod 1:// of_uintK modz_small //.
  apply bound_abs; smt (le_modz to_uint_cmp gt0_pow2 modz_cmp).
qed.

lemma nosmt to_uintNE w:
 to_uint (-w) = (modulus - to_uint w) %% modulus.
proof.
rewrite to_uintN.
by have /= ->:= (modzMDl 1).
qed.

lemma nosmt of_intNE (n:int):
  of_int (-n) = of_int (modulus - n).
proof.
rewrite of_intN.
apply word_modeqP; congr.
rewrite to_uintN !of_uintK modzNm.
by have /= ->:= (modzMDl 1).
qed.

lemma of_int_modulus: of_int modulus = BitWord.zero.
proof. rewrite !of_intE modzz modz_small; smt(gt0_modulus). qed.

lemma to_uint_onew: to_uint onew = max_uint.
proof. by rewrite oneE of_uintK modz_small //; smt(ge2_modulus). qed.

lemma onewS: onew + BitWord.one = BitWord.zero.
proof.
apply word_modeqP; congr.
by rewrite to_uintD to_uint0 to_uint_onew to_uint1 max_uintS modzz.
qed.

lemma map2_w2bits_w2bits f w1 w2 : map2 f (w2bits w1) (w2bits w2) = w2bits (map2 f w1  w2).
proof. by rewrite map2_w2bits bits2wK // size_map2 minrE !size_w2bits. qed.

lemma map_w2bits_w2bits f w : map f (w2bits w) = w2bits (map f w).
proof. by rewrite map_w2bits bits2wK 2:// size_map size_w2bits. qed.

lemma nosmt to_uintD_disjoint w1 w2:
 w1 `&` w2 = BitWord.zero =>
 to_uint (w1 + w2) = to_uint w1 + to_uint w2.
proof.
move=> H; have H0: to_uint (w1 `&` w2) = 0 by smt(to_uint0).
rewrite to_uintD_small //.
move: H0; rewrite !to_uintE.
rewrite andE => H0.
apply bs2int_add_disjoint; rewrite ?size_w2bits //.
by rewrite -H0 map2_w2bits_w2bits.
qed.

lemma nosmt orw_disjoint w1 w2:
 w1 `&` w2 = BitWord.zero => w1 `|` w2 = w1 + w2.
proof.
move=> H; have H0: to_uint (w1 `&` w2) = 0 by smt(to_uint0).
apply word_modeqP; congr.
rewrite to_uintD_disjoint //.
move: H0; rewrite !to_uintE andE => H0.
by rewrite orE -bs2int_or_add ?size_mkseq // 1:-H0 map2_w2bits_w2bits.
qed.

lemma nosmt to_uint_orw_disjoint w1 w2:
 w1 `&` w2 = zero =>
 to_uint (w1 `|` w2) = to_uint w1 + to_uint w2.
proof. by move=> *; rewrite orw_disjoint // to_uintD_disjoint. qed.

lemma nosmt ule_andN0 (x y: t):
 x `&` invw y = BitWord.zero =>
 x \ule y.
proof.
rewrite andwC => ?; have: to_uint (invw y `&` x) = 0 by smt(to_uint0).
rewrite !to_uintE andE invE => ?.
have ->: x \ule y = (0 <= (to_uint y - to_uint x)) by rewrite uleE /#.
rewrite !to_uintE; apply bs2int_sub_common.
+ by rewrite !size_w2bits. 
by rewrite map_w2bits_w2bits map2_w2bits_w2bits.
qed.

lemma nosmt ule_andw x y:
 x `&` y \ule x.
proof.
rewrite andwC; apply ule_andN0.
by rewrite -andwA andw_invw andw0.
qed.

lemma nosmt to_uint_ule_andw (x y: t):
 to_uint (x `&` y) <= to_uint x.
proof. have := ule_andw x y; by rewrite uleE. qed.

lemma nosmt ule_orw x y:
 x \ule x `|` y.
proof.
have {1}->: x = (x`|`y) `&` (x`|`invw y).
 rewrite -{1}orw0.
 have :=(andw_invw y); rewrite /zerow => <-.
 by rewrite orw_andwDr.
by apply ule_andw.
qed.

lemma nosmt subw_xorw w1 w2:
 invw w1 `&` w2 = BitWord.zero => w1 - w2 = w1 `^` w2.
proof.
move=> H; have H0: to_uint (invw w1 `&` w2) = 0 by smt(to_uint0).
apply word_modeqP; congr.
rewrite to_uintB.
 by apply ule_andN0; rewrite andwC.
move: H0; rewrite !to_uintE andE invE => H0.
rewrite xorE.
rewrite -bs2int_xor_sub ?size_mkseq //.
+ by rewrite map_w2bits_w2bits map2_w2bits_w2bits.
by rewrite map2_w2bits_w2bits.
qed.

lemma nosmt orw_xpnd w1 w2: w1 `|` w2 = w1 - w1 `&` w2 + w2.
proof.
rewrite subw_xorw.
 by rewrite andwA (andwC (invw w1)) andw_invw and0w.
rewrite -orw_disjoint.
 by rewrite andwDl -andwA andwK xorwK.
rewrite !orw_xorw.
have ->: w1 `^` (w1 `&` w2) `&` w2 = zerow.
 by rewrite andwDl -andwA andwK xorwK.
by rewrite -!xorwA xorw0 (xorwC w2).
qed.

lemma ones_compl w: w + invw w = onew.
proof.
have:= orw_invw w.
rewrite orw_xpnd andw_invw => <-.
by ring.
qed.

lemma nosmt twos_compl (x: t):  -x = invw x + BitWord.one.
proof.
apply (addrI x); rewrite addrA ones_compl onewS.
by ring.
qed.

lemma minus_one: -one = onew.
proof.
rewrite twos_compl -orw_disjoint.
 by rewrite andwC andw_invw.
by rewrite orwC orw_invw.
qed.

lemma nosmt to_uint_invw w: to_uint (invw w) = max_uint - to_uint w.
proof.
rewrite -to_uint_onew -to_uintB.
 rewrite uleE to_uint_onew.
 smt(to_uint_cmp).
by congr; rewrite -(ones_compl w); ring.
qed.

abbrev masklsb k = of_int (2^(max 0 k) - 1).

lemma masklsbNeg k:
 k <= 0 => masklsb k = zerow.
proof. move=> ?; rewrite ler_maxl //. qed.

lemma masklsbE k i:
 (masklsb k).[i] = 0 <= i < min k size.
proof.
case: (0 <= k) => H; last first.
+ by rewrite ler_maxl 1:/# /=; smt(ge0_size). 
rewrite ler_maxr 1://. 
case: (0 <= i < size) => Hi; last by rewrite get_out /#.
rewrite of_intE.
case: (size <= k) => H0.
+ rewrite powm1_mod // get_bits2w //.
  have /=:= (bs2int_nseq true size); rewrite ge0_size /= => <-.
  have:= bs2intK (nseq size true); rewrite size_nseq ler_maxr 1:/# => ->.
  by rewrite nth_nseq //#. 
rewrite modz_small; first by smt(gt0_pow2 ler_weexpn2l).
rewrite get_bits2w //.
have /= := (bs2int_nseq true k); rewrite H /= => <-.
rewrite (bs2int_pad (size - k)).
pose L:= _++_.
have:= bs2intK L; rewrite size_cat !size_nseq !ler_maxr 1,2:/#.
have -> ->: k + (size-k) = size by smt().
rewrite /L nth_cat size_nseq ler_maxr //=.
by case: (i < k) => ?; rewrite nth_nseq /#.
qed.

hint simplify masklsbE.

lemma nosmt shrl_andmaskN k w:
 0 <= k =>
 w `>>>` k `<<<` k = w `&` invw (masklsb k).
proof. by move=> Hk; apply wordP => i Hi /= /#. qed.

lemma nosmt shlw_andmask k1 k2 w:
 0 <= k1 <= k2 < size =>
 (w `<<<` k1) `&` masklsb k2 = (w `&` masklsb (k2-k1)) `<<<` k1.
proof.
move=> *; apply/wordP => i Hi /=; rewrite !Hi /= /min.
smt(get_out).
qed.

lemma nosmt andmask_shrw k1 k2 w:
 0 <= k2 < k1 < size =>
 (w `&` masklsb k1) `>>>` k2
 = (w `>>>` k2) `&` masklsb (k1-k2).
proof.
move=> *; apply/wordP => i Hi /=; rewrite !Hi /min /=.
smt(get_out).
qed.

lemma nosmt andmask_shlw k1 k2 w:
 0 <= k1 < size =>
 (w `&` masklsb k1) `<<<` k2
 = (w `<<<` k2) `&` masklsb (k1+k2).
proof.
move=> *; apply/wordP => i Hi /=; rewrite Hi /= /min.
smt(get_out).
qed.

lemma nosmt shrw_shlw_disjoint k1 k2 w1 w2:
 0 <= k1 < size <= k1+k2 =>
 (w1 `>>>` k1) `&` (w2 `<<<` k2) = zero.
proof.
move=> *; apply/wordP => i Hi /=; rewrite Hi /= /min.
smt(get_out).
qed.

lemma nosmt andmaskK k w:
 size <= k =>  w `&` masklsb k = w.
proof. by move=> *; apply/wordP => i Hi /= /#. qed.

lemma nosmt shrw_andmaskK k1 k2 w:
 0 <= k1 < size <= (k1+k2)%Int =>
 (w `>>>` k1) `&` masklsb k2 = (w `>>>` k1).
proof.
move=> *; apply/wordP => i Hi /=; rewrite !Hi /= /min.
smt(get_out).
qed.

lemma mask_and_mask k1 k2:
 0 <= k1 => 0 <= k2 =>
 (masklsb k1 `&` masklsb k2) = masklsb (min k1 k2).
proof. by move=> *; apply/wordP => i Hi /= /#. qed.

lemma nosmt shrw_shlw_shlw k1 k2 x:
 0 <= k1 < k2 =>
 x `>>>` k1 `<<<` k2 = (x `&` invw (masklsb k1)) `<<<` (k2-k1).
proof. by move=> *; apply/wordP => i Hi /= /#. qed.

lemma nosmt shrw_shlw_shrw k1 k2 x:
 0 <= k2 <= k1 < size =>
 x `>>>` k1 `<<<` k2 = (x `&` invw (masklsb k1)) `>>>` (k1-k2).
proof.
move=> *; apply/wordP => i Hi /=; rewrite !Hi /= /min.
smt(get_out).
qed.

lemma nosmt shlw_shrw_shlw k1 k2 x:
 0 <= k2 <= k1 < size =>
 x `<<<` k1 `>>>` k2 = (x `&` masklsb (size-k1)) `<<<` (k1-k2).
proof.
move=> *; apply/wordP => i Hi /=; rewrite !Hi /= /min.
smt(get_out).
qed.

lemma nosmt shlw_shrw_shrw k1 k2 x:
 0 <= k1 < k2 < size =>
 x `<<<` k1 `>>>` k2 = (x `&` masklsb (size-k1)) `>>>` (k2-k1).
proof. by move=> *; apply/wordP => i Hi /=; rewrite !Hi /= /#. qed.

lemma nosmt splitwE k w:
 0 <= k =>
 to_uint w = to_uint (w `&` masklsb k) + 2^k * to_uint (w `>>>` k).
proof.
move=> ?; rewrite to_uint_and_mod ler_maxr // to_uint_shr //.
by rewrite {1}(divz_eq (to_uint w) (2^k)); ring.
qed.

op splitBits k w = (w `&` masklsb k, w `>>>` k).

lemma nosmt splitBits_disjoint k w:
 0 <= k =>
 (splitBits k w).`1 `&` ((splitBits k w).`2 `<<<` k) = BitWord.zero.
proof.
move => *; rewrite /splitBits /= shrl_andmaskN //.
by rewrite andwA -(andwA w) (andwC _ w) andwA andwK -andwA andw_invw andw0.
qed.

lemma nosmt to_uint_splitBits k w:
 0 <= k =>
 to_uint (splitBits k w).`1 + 2^k * to_uint (splitBits k w).`2 = to_uint w.
proof. by move=> ?; rewrite eq_sym (splitwE k w). qed.

op splitMask mask w = (w `&` mask, w `&` invw mask).

abbrev splitAt k = splitMask (masklsb k).

lemma splitMask_and0 mask w:
 (splitMask mask w).`1 `&` (splitMask mask w).`2 = BitWord.zero.
proof.
rewrite /splitMask /=.
by rewrite (andwC w) -andwA (andwA w) andwK (andwC w) andwA andw_invw and0w.
qed.

lemma nosmt splitMask_add mask w:
 (splitMask mask w).`1 + (splitMask mask w).`2 = w.
proof.
rewrite -orw_disjoint; first by apply (splitMask_and0 mask w).
by rewrite /splitMask /= !(andwC w) -andw_orwDl orw_invw and1w.
qed.

lemma nosmt splitAtP k w:
 0 <= k <= size =>
 to_uint (splitAt k w).`1 = to_uint w %% 2^k
 /\ to_uint (splitAt k w).`2 = 2^k * (to_uint w %/ 2^k).
proof.
move=> /> *.
rewrite /splitMask /= -shrl_andmaskN //; split.
+ by rewrite to_uint_and_mod ler_maxr.
rewrite to_uint_shl // to_uint_shr // modz_small //; last by smt(to_uint_cmp).
apply bound_abs; split.
+ smt(divr_ge0 divz_ge0 gt0_pow2 to_uint_cmp).
move=> *.
by apply (ler_lt_trans (to_uint w)); smt(leq_trunc_div gt0_pow2 to_uint_cmp).
qed.

op wmulhs (v1 v2: t) = 
  of_int (to_sint v1 * to_sint v2 %/ modulus).

theory ALU.

op SF_of (w : t) = w.[size - 1].

op ZF_of (w : t) = w = zero.

(*
  let OF = in
  let CF = in
  let SF = in
  let PF = in
  let ZF = in
  (OF, CF, SF, PF, ZF).
*)

op rflags_of_bwop (w : t) =
  let OF = false in
  let CF = false in
  let SF = SF_of w in 
  let PF = undefined_flag in
  let ZF = ZF_of w in
  (OF, CF, SF, PF, ZF).

op rflags_of_aluop (w : t) (vu vs : int) =
  let OF = to_sint w <> vs in
  let CF = to_uint w <> vu in
  let SF = SF_of w in
  let PF = undefined_flag in
  let ZF = ZF_of w in
  (OF, CF, SF, PF, ZF).

op rflags_of_andn (w: t) =
  let OF = false in
  let CF = false in
  let SF = SF_of w in
  let PF = undefined_flag in
  let ZF = ZF_of w in
  (OF, CF, SF, PF, ZF).

op rflags_of_popcnt (w: t) =
  let OF = false in
  let CF = false in
  let SF = false in
  let PF = false in
  let ZF = ZF_of w in
  (OF, CF, SF, PF, ZF).

op rflags_of_aluop_nocf_w (w : t) (vs : int) =
  let OF = to_sint w <> vs in
  let SF = SF_of w in
  let PF = undefined_flag in
  let ZF = ZF_of w in
  (OF, SF, PF, ZF, w).

op rflags_of_aluop_w (w : t) (vu vs : int) =
  flags_w (rflags_of_aluop w vu vs) w.

op rflags_of_bwop_w (w : t) =
  flags_w (rflags_of_bwop w) w.

op set0_XX_ = (false,false,false,false,false, of_int 0).

op ADD_XX (v1 v2 : t)  =
  rflags_of_aluop_w 
    (v1 + v2) 
    (to_uint v1 + to_uint v2)
    (to_sint v1 + to_sint v2).

op SUB_XX (v1 v2 : t) =
  rflags_of_aluop_w
    (v1 - v2)
    (to_uint v1 - to_uint v2)
    (to_sint v1 - to_sint v2).

op CMOVcc_XX (b:bool) (w2 w3: t) =
  if b then w2 else w3.

op wdwordu hi lo = to_uint hi * modulus + to_uint lo.
op wdwords hi lo = to_sint hi * modulus + to_uint lo.

op MUL_XX (v1 v2: t) =
  let (hi,lo) = mulu v1 v2 in
  let ov = wdwordu hi lo in
  let ov = modulus - 1 < ov in
  flags_w2 (rflags_of_mul ov) hi lo.

op IMUL_overflow (hi lo: t) : bool =
  let ov = wdwords hi lo in
  (ov < min_sint) || (max_sint < ov).

op IMUL_XX (v1 v2: t) =
  let lo = v1 * v2 in
  let hi = wmulhs v1 v2 in
  let ov = IMUL_overflow hi lo in
  flags_w2 (rflags_of_mul ov) hi lo.

op IMULt_XX (v1 v2: t) =
  let lo = v1 * v2 in
  let hi = wmulhs v1 v2 in
  let ov = IMUL_overflow hi lo in
  flags_w (rflags_of_mul ov) lo.

op IMULr_XX = IMULt_XX.
op IMULri_XX = IMULt_XX.

op DIV_XX (hi lo dv: t) =
  let dd = wdwordu hi lo in
  let dv = to_uint dv in
  let q  = dd %/ dv in
  let r  = dd %% dv in
(* The next lines are commented:
   The point is that the (Coq) semantic raise an error if "dv = 0 || ov".
   But the extraction need to be correct only on safe program, so it is not necessary. *)
(*let ov = max_uint < q in
  let (q, r) = if dv = 0 || ov then (0, 0) else (q, r) in *)
  flags_w2 rflags_undefined (of_int q) (of_int r).

op IDIV_XX (hi lo dv: t) =
  let dd = wdwords hi lo in
  let dv = to_sint dv in
  let q  = dd %/ dv in
  let r  = dd %/ dv in
(* Same comment than for DIV_XX *)
(*let ov = (q <? wmin_signed sz)%Z || (q >? wmax_signed sz)%Z in
  let (q, r) = if dv = 0 || ov then (0,0) else (q, r) in *)
  flags_w2 rflags_undefined (of_int q) (of_int r). 

op CQO_XX (w:t) =
  of_int (if SF_of w then -1 else 0).

op add_carry (x y c: int) : t =
  of_int (x + y + c).

op ADC_XX (v1 v2 : t) (c: bool) =
  let c = b2i c in
  rflags_of_aluop_w
    (add_carry (to_uint v1) (to_uint v2) c)
    (to_uint v1 + to_uint v2 + c)
    (to_sint v1 + to_sint v2 + c).

op ADCX_XX (v1 v2: t) (c:bool) = addc v1 v2 c.
op ADOX_XX (v1 v2: t) (c:bool) = addc v1 v2 c.

op MULX_XX (v1 v2: t) = mulu v1 v2.
op MULX_lo_hi_XX (v1 v2: t) = let (hi,lo) = mulu v1 v2 in (lo, hi).
op MULX_hi_XX (v1 v2: t) = (mulu v1 v2).`1.

op sub_borrow (x y c: int) : t =
  of_int (x - y - c).

op SBB_XX (v1 v2 : t) (c:bool) =
  let c = b2i c in
  rflags_of_aluop_w
    (sub_borrow (to_uint v1) (to_uint v2) c)
    (to_uint v1 - (to_uint v2 + c))
    (to_sint v1 - (to_sint v2 + c)).

op NEG_XX (w: t) =
  let vs = - to_sint w in
  let v  = - w in
  let OF = to_sint v <> vs in
  let CF = w <> of_int 0 in
  let SF = SF_of v in
  let PF = undefined_flag in
  let ZF = ZF_of v in
  (OF, CF, SF, PF, ZF, v).

op INC_XX (w: t) =
  rflags_of_aluop_nocf_w
    (w + of_int 1)
    (to_sint w + 1).

op DEC_XX (w: t) =
  rflags_of_aluop_nocf_w
    (w - of_int 1)
    (to_sint w - 1).

op BT_XX (x y: t) = x.[to_uint y %% size].

op LEA_XX (addr: t) = addr.

op TEST_XX (x y: t) =
  rflags_of_bwop (x `&` y).

op CMP_XX (x y: t) =
  rflags_of_aluop 
     (x - y)
     (to_uint x - to_uint y) 
     (to_sint x - to_sint y).

op AND_XX (v1 v2: t) =
  rflags_of_bwop_w (v1 `&` v2).

op ANDN_XX (v1 v2: t) =
  let w = (invw v1) `&` v2 in
  flags_w (rflags_of_andn w) w.

op OR_XX (v1 v2: t) =
  rflags_of_bwop_w (v1 `|` v2).

op XOR_XX (v1 v2: t) =
  rflags_of_bwop_w (v1 +^ v2).

op NOT_XX (v: t) =
  invw v.

op LZCNT_XX (w:t) =
  let v = of_int (lzcnt (rev (w2bits w))) in
  (undefined_flag, ZF_of w, undefined_flag, undefined_flag, ZF_of v, v).

lemma DEC_XX_counter n (c:t) :
  c <> zero =>
  (n - to_uint c + 1 = n - to_uint (DEC_XX c).`5 /\
  (DEC_XX c).`4 = ((DEC_XX c).`5 = zero)) /\
  (n - to_uint c + 1 < n <=> ! (DEC_XX c).`4).
proof.
  move=> hc0; rewrite /DEC_XX /rflags_of_aluop_nocf_w /rflags_of_aluop_nocf /ZF_of => /=.
  have -> : (c - one = zero) <=> (to_uint (c - one) = 0).
  + by split => [-> // | h]; apply (canRL _ _ _ _ to_uintK).
  have hc0': to_uint c <> 0.
  + by apply negP => heq; apply hc0; rewrite -(to_uintK c) heq.
  rewrite to_uintB /= 1:uleE /=; smt (to_uint_cmp).
qed.

op POPCNT_XX (v: t) =
  let vb = w2bits v in
  let wcnt = of_int (count idfun vb) in
  flags_w (rflags_of_popcnt wcnt) wcnt.

op PEXT_XX (v m: t) =
  let vbi = filter (fun i => m.[i]) (iota_ 0 size) in
  bits2w (map (fun i => v.[i]) vbi).

op bitpdep (w: t) (i:int) (mask: bool list) =
  with mask = "[]" => []
  with mask = b :: mask' => if b then w.[i] :: bitpdep w (i+1) mask' else false :: bitpdep w i mask'.

op PDEP_XX (v m: t) =
  bits2w (bitpdep v 0 (w2bits m)).

end ALU.

end BitWord.

theory W8.
  abbrev [-printing] size = 8.
  clone include BitWord with op size <- 8
  rename [op, lemma] "_XX" as "_8"
  proof gt0_size by done.

  op (`>>`) (w1 w2 : W8.t) = w1 `>>>` (to_uint w2 %% size).
  op (`<<`) (w1 w2 : W8.t) = w1 `<<<` (to_uint w2 %% size).

  lemma shr_div w1 w2 : to_uint (w1 `>>` w2) = to_uint w1 %/ 2^ (to_uint w2 %% size).
  proof.
    rewrite -{1}(to_uintK w1) /(`>>`) shrDP; 1: smt (modz_cmp).
    rewrite of_uintK to_uint_mod modz_small 2://.
    apply bound_abs; apply divz_cmp; 1: by apply gt0_pow2.
    by have:= to_uint_cmp w1; smt (gt0_pow2).
  qed.

  lemma shr_div_le w1 i : 0 <= i < size =>
       to_uint (w1 `>>` (of_int i)) = to_uint w1 %/ 2^i.
  proof.
    move=> hi;rewrite shr_div of_uintK.
    rewrite (modz_small i);1: smt (pow2_8).
    by rewrite modz_small.
  qed.

  op (`|>>|`) (w1 w2 : W8.t) = w1 `|>>>|` (to_uint w2 %% size).
  op (`|<<|`) (w1 w2 : W8.t) = w1 `|<<<|` (to_uint w2 %% size).

  lemma rol_xor_shft w i : 0 < i < size =>
    w `|<<<|` i = (w `<<` of_int i) +^ (w `>>` of_int (size - i)).
  proof.
    move=> hi; rewrite /(`<<`) /(`>>`) !of_uintK /=.
    by rewrite !(modz_small _ 256) 1,2:/# !modz_small 1,2:/# rol_xor 1:/#.
  qed.

  op (`|>>`) (w1 w2 : W8.t) = sar w1 (to_uint w2 %% size).

  op SETcc (b: bool) = b ? W8.one : W8.zero.

  theory SHIFT.

  op shift_mask i = to_uint i %% 32.
  
  op ROR_8 (v: t) (i: W8.t) =
    let i = shift_mask i in
    if i = 0 then (undefined_flag, undefined_flag, v) 
    else
      let r = v `|>>>|` i in
      let CF = ALU.SF_of r in
      let OF = if i = 1 then CF <> ALU.SF_of v else undefined_flag in
      (OF , CF,  r)
  axiomatized by ROR_8_E.
  
  op ROL_8 (v: t) (i: W8.t) =
    let i = shift_mask i in
    if i = 0 then(undefined_flag, undefined_flag, v)
    else
      let r = v `|<<<|` i in
      let CF = lsb r in
      let OF = if i = 1 then ALU.SF_of r <> CF else undefined_flag in
      (OF, CF, r)
  axiomatized by ROL_8_E.
  
  op im i = 
    if size = 8 then i %% 9
    else if size = 16 then i %% 17
    else i.

  op RCL_8 (v: t) (i: W8.t) (cf:bool) =
    let i  = shift_mask i in
    let im = im i in
    let r  = fun j => if j = 0 then cf else v.[j-1] in
    let r  = fun j => r ((j - i) %% 9) in
    let CF = r 0 in 
    let r  = init (fun j => r (j+1)) in
    let OF = if i = 1 then (ALU.SF_of r <> CF) else undefined_flag in
    (OF, CF, r).
  
  op RCR_8 (v: t) (i: W8.t) (cf:bool) =
    let i  = shift_mask i in
    let im = im i in
    let r  = fun j => if j = 0 then cf else v.[j-1] in
    let r  = fun j => r ((j + i) %% 9) in
    let OF = if i = 1 then ALU.SF_of  v <> cf else undefined_flag in
    let CF = r 0 in 
    let r  = init (fun j => r (j+1)) in
    (OF, CF, r).

  op rflags_OF (i:int) (r:t) (rc OF:bool) =
    let OF = if i = 1 then OF else undefined_flag in
    let CF = rc in
    let SF = ALU.SF_of r in
    let PF = undefined_flag in
    let ZF = ALU.ZF_of r in
    (OF, CF, SF, PF, ZF, r).

  op SHL_8  (v: t) (i: W8.t) =
    let i = shift_mask i in
    if i = 0 then flags_w rflags_undefined v
    else
      let rc = ALU.SF_of (v `<<<` (i - 1)) in 
      let r  = v `<<<` i in
      rflags_OF i r rc (ALU.SF_of r ^^ rc).

  op SHLD_8 (v1 v2: t) (i: W8.t) =
    let i = shift_mask i in
    if i = 0 then flags_w rflags_undefined v1
    else
      let rc = ALU.SF_of (v1 `<<<` (i - 1)) in
      let r1 = v1 `<<<` i in
      let r2 = v2 `>>>` (size - i) in
      let r  = r1 +^ r2 in
      rflags_OF i r rc (ALU.SF_of r ^^ rc).
  
  op SHR_8 (v: t) (i: W8.t) =
    let i = shift_mask i in 
    if i = 0 then flags_w rflags_undefined v 
    else
      let rc = lsb (v `>>>` i -1) in
      let r  = v `>>>` i in
      rflags_OF i r rc (ALU.SF_of r).
  
  op SHRD_8 (v1 v2: t) (i: W8.t) =
    let i = shift_mask i in
    if i = 0 then flags_w rflags_undefined v1
    else
      let rc = lsb (v1 `>>>` i - 1) in
      let r1 = v1 `>>>` i in
      let r2 = v2 `<<<` (size - i) in
      let r  = r1 +^ r2 in
      rflags_OF i r rc (ALU.SF_of r ^^ ALU.SF_of v1).
  
  op SAR_8 (v: t) (i: W8.t) =
    let i = shift_mask i in 
    if i = 0 then flags_w rflags_undefined v
    else
      let rc = lsb (sar v (i - 1)) in
      let r  = sar v i in
      rflags_OF i r rc false.

end SHIFT.
end W8. export W8 W8.ALU W8.SHIFT.

abstract theory WT.
  type t.
  op size : int.
  axiom gt0_size : 0 < size.

  op "_.[_]" : t -> int -> bool.
  op init : (int -> bool) -> t.

  op andw : t -> t -> t.
  op orw  : t -> t -> t.
  op (+^) : t -> t -> t.
  op invw : t -> t.

  op wmulhs : t -> t -> t.

  op (+) : t -> t -> t.
  op [-] : t -> t. 
  op ( * ) : t -> t -> t.

  op (`>>>`) : t -> int -> t.
  op (`<<<`) : t -> int -> t.
  op (`>>`) : t -> W8.t -> t.
  op (`|>>`) : t -> W8.t -> t.
  op (`<<`) : t -> W8.t -> t.
  op rol : t -> int -> t.
  op of_int : int -> t.
  op to_uint : t -> int.
  op to_sint : t -> int.

  op bits : t -> int -> int -> bool list.

  abbrev (`|<<<|`) = rol.

  axiom initiE (f : int -> bool) (i : int) : 0 <= i < size => (init f).[i] = f i.

  axiom andwE (w1 w2 : t) (i : int) : (andw w1 w2).[i] = (w1.[i] /\ w2.[i]).
  axiom orwE  (w1 w2 : t) (i : int) : (orw  w1 w2).[i] = (w1.[i] \/ w2.[i]).
  axiom xorwE (w1 w2 : t) (i : int) : (w1 +^ w2).[i] = (w1.[i] ^^ w2.[i]).
  axiom invwE (w:t) (i:int) : (invw w).[i] = (0 <= i < size /\ !w.[i]).

  axiom wordP (w1 w2 : t) :
    w1 = w2 <=> forall (i : int), 0 <= i < size => w1.[i] = w2.[i].

  axiom to_uint_cmp (x : t) : 0 <= to_uint x < 2^size.

  op int_bit x i = (x%%2^size) %/ 2 ^ i %% 2 <> 0.

  axiom of_intwE x i :
   (of_int x).[i] = (0 <= i < size /\ int_bit x i).

  axiom get_to_uint w i : w.[i] = (0 <= i < size /\ to_uint w %/ 2 ^ i %% 2 <> 0).

  axiom bitsE w k len : bits w k len = mkseq (fun (i:int) => w.[k+i]) len.

  axiom bits_divmod w i j: 0 <= i => 0 <= j =>
    bs2int (bits w i j) = ((to_uint w) %/ 2^i) %% 2^j.

  axiom to_uintRL (w:t) (x:int) : to_uint w = x %% 2^size => w = of_int x.

  axiom to_uint_bits w : to_uint w = bs2int (bits w 0 size).

  axiom of_uintK (x : int) : to_uint (of_int x) = x %% 2^size.

  axiom to_uintK : cancel to_uint of_int.

  axiom of_int_mod (x : int) : of_int (x %% 2^size) = of_int x.

  axiom and_mod k w :
    0 <= k =>
      andw w (of_int (2^k - 1)) = of_int (to_uint w %% 2^k).

  axiom rol_xor_shft w i : 0 < i < size =>
    w `|<<<|` i = (w `<<` W8.of_int i) +^ (w `>>` W8.of_int (size - i)).

end WT.

abstract theory W_WS.

  op sizeS : int.
  op sizeB : int.
  op r : int.
  axiom gt0_r : 0 < r.
  axiom sizeBrS : sizeB = r * sizeS.

  clone import WT as WS with op size <- sizeS.
  clone import WT as WB with op size <- sizeB.

  clone export MonoArray as Pack with
    type elem <- WS.t,

    op dfl <- WS.of_int 0,
    op size <- r
    proof ge0_size by smt (gt0_r)
    rename [type] "t" as "pack_t"
           [lemma] "tP" as "packP".

  hint simplify Pack.map_to_list@1.
  hint simplify Pack.map2_to_list@1.

  lemma le_size : sizeS <= sizeB.
  proof. rewrite sizeBrS;smt (gt0_r WS.gt0_size WB.gt0_size). qed.

  lemma in_bound i j : 0 <= i < r => 0 <= j < sizeS => 0 <= i * sizeS + j < sizeB.
  proof.
    move=> hi hj;rewrite sizeBrS;have : i * sizeS + j < (i+1) * sizeS by smt().
    rewrite mulzDl /= => H; split; first smt().
    move => ?; apply (ltr_le_trans _ _ _ H).
    have ->: i * sizeS + sizeS = (i+1)*sizeS by smt().
    by apply ler_wpmul2r; smt().
  qed.

  (* ------------------------------------------------ *)

  op sigextu'B   (w:WS.t) = WB.of_int (WS.to_sint w).
  op zeroextu'B  (w:WS.t) = WB.of_int (WS.to_uint w).
  op truncateu'S (w:WB.t) = WS.of_int (WB.to_uint w).

  hint exact : WS.gt0_size WB.gt0_size.

  lemma size_div : sizeS %| sizeB.
  proof. by rewrite dvdzP sizeBrS;exists r. qed.

  lemma div_size : sizeB %/ sizeS = r.
  proof. rewrite sizeBrS mulzK; smt (WS.gt0_size). qed.

  op (\bits'S) (w:WB.t) i = WS.init (fun j => w.[ i * sizeS + j])
  axiomatized by bits'SE.

  op unpack'S (w:WB.t) : pack_t =
    Pack.init (fun i => w \bits'S i)
  axiomatized by unpack'SE.

  abbrev to_list (w:WB.t) : WS.t list = 
    map ((\bits'S) w) (iotared 0 r).

  op pack'R_t (ws:pack_t) =
    WB.init (fun i => ws.[i %/ sizeS].[i %% sizeS])
  axiomatized by pack'RE.

  abbrev pack'R (ws:WS.t list) = pack'R_t (Pack.of_list ws).

  lemma pack'RwE (ws:pack_t) i : 0 <= i < sizeB =>
    (pack'R_t ws).[i] = ws.[i %/ sizeS].[i %% sizeS].
  proof. by move=> hi;rewrite pack'RE initiE //. qed.

  lemma get_unpack'S w i : 0 <= i < r =>
    (unpack'S w).[i] = w \bits'S i.
  proof. rewrite unpack'SE; apply initiE. qed.

  lemma bits'SiE w i j : 0 <= j < sizeS =>
    (w \bits'S i).[j] = w.[i * sizeS + j].
  proof. by move=> hj; rewrite bits'SE initiE. qed.

  lemma get_bits'S (w:WB.t) i :
    0 <= i < sizeB =>
    w.[i] = (w \bits'S (i%/ sizeS)).[i %% sizeS].
  proof.
    by move=> hi; rewrite bits'SE WS.initiE /= -?divz_eq; 1:by apply modz_cmp.
  qed.

  lemma get_out (w:WB.t) i :
     !(0 <= i < r) =>
     w \bits'S i = WS.of_int 0.
  proof.
    move=> hi;apply WS.wordP => k hk.
    rewrite bits'SiE 1:// WS.of_intwE /WS.int_bit /= get_to_uint sizeBrS /#.
  qed.

  lemma get_zero i : WB.of_int 0 \bits'S i = WS.of_int 0.
  proof.
    apply WS.wordP => k hk.
    by rewrite bits'SiE 1:// WS.of_intwE /WS.int_bit /= get_to_uint /= WB.of_uintK.
  qed.

  lemma unpack'SK w : pack'R_t (unpack'S w) = w.
  proof.
    apply wordP => i hi; rewrite pack'RE initiE //= get_bits'S //.
    by rewrite get_unpack'S //;apply divz_cmp => //;rewrite -sizeBrS.
  qed.

  lemma pack'RbE ws i : 0 <= i < r => pack'R_t ws \bits'S i = ws.[i].
  proof.
    move=> hr;apply WS.wordP => j hj.
    rewrite bits'SiE // pack'RE initiE /= ?in_bound //.
    have h : 0 <= j < `|sizeS| by smt().
    by rewrite modzMDl divzMDl 1:/# divz_small ?modz_small.
  qed.

  lemma pack'RK ws : unpack'S (pack'R_t ws) = ws.
  proof. by apply packP => i hi; rewrite get_unpack'S // pack'RbE. qed.

  lemma wordP (w1 w2 :WB.t) : (forall i, 0 <= i < r => w1 \bits'S i = w2 \bits'S i) => w1 = w2.
  proof.
    move=> h; rewrite -(unpack'SK w1) -(unpack'SK w2); congr.
    by apply Pack.packP => i hi; rewrite !get_unpack'S 1,2://; apply h.
  qed.

  lemma allP (w1 w2 :WB.t) : all (fun i => w1 \bits'S i = w2 \bits'S i) (iotared 0 r) => w1 = w2.
  proof. 
    rewrite allP => h; apply wordP => i hi; apply h.
    by rewrite iotaredE (mema_iota 0 r). 
  qed.

  op map (f:WS.t -> WS.t) (w:WB.t) =
    pack'R_t (map f (unpack'S w))
  axiomatized by mapE.

  op map2 (f:WS.t -> WS.t -> WS.t) (w1 w2:WB.t) =
    pack'R_t (map2 f (unpack'S w1) (unpack'S w2))
  axiomatized by map2E.

  lemma mapbE f w i : 0 <= i < r =>
    (map f w) \bits'S i = f (w \bits'S i).
  proof.
    by move=> hi;rewrite mapE pack'RbE // mapiE // unpack'SE initiE.
  qed.

  lemma map2bE f w1 w2 i : 0 <= i < r =>
    (map2 f w1 w2) \bits'S i = f (w1 \bits'S i) (w2 \bits'S i).
  proof.
    by move=> hi;rewrite map2E pack'RbE // map2iE // !unpack'SE !initiE.
  qed.

  lemma map_pack'R f ws : 
    map f (pack'R ws) = pack'R (mapN f (WS.of_int 0) ws r).
  proof. 
    apply wordP => i hi.
    by rewrite mapbE 1:// pack'RbE 1:// pack'RbE 1:// -map_of_list mapiE.
  qed.

  lemma nth_to_list w i : 
    0 <= i < r =>
    nth (WS.of_int 0) (to_list w) i = w \bits'S i.
  proof.
    move=> hi; rewrite iotaredE (nth_map 0) 1:size_iota /max 1:gt0_r 1:// nth_iota //. 
  qed.

  lemma map_to_list f w : 
    map f w = pack'R (map f (to_list w)). 
  proof. 
    apply wordP => i hi.
    rewrite mapbE 1:// pack'RbE 1:// get_of_list 1:// iotaredE. 
    have hs : 0 <= i && i < size (iota_ 0 r) by rewrite size_iota /max gt0_r.
    rewrite (nth_map (WS.of_int 0)) 1:size_map 1://. 
    by rewrite (nth_map 0) 1:// nth_iota. 
  qed.
    
  hint simplify map_pack'R @0, map_to_list @1.

  lemma map2_pack'R f ws1 ws2 : 
    map2 f (pack'R ws1) (pack'R ws2) = pack'R (mapN2 f (WS.of_int 0) (WS.of_int 0) ws1 ws2 r).
  proof. 
    apply wordP => i hi.
    by rewrite map2bE 1:// !pack'RbE 1..3:// -map2_of_list map2iE.
  qed.

  lemma map2_to_list f w1 w2 : 
    map2 f w1 w2 = pack'R (map2 f (to_list w1) (to_list w2)). 
  proof. 
    apply wordP => i hi.
    rewrite map2bE 1:// pack'RbE 1:// get_of_list 1:// iotaredE. 
    have hs : 0 <= i && i < size (iota_ 0 r) by rewrite size_iota /max gt0_r.
    rewrite (nth_map2 (WS.of_int 0) (WS.of_int 0)) 1:size_map 1://. 
    + by rewrite size_map.
    by rewrite !(nth_map 0) 1,2:// nth_iota. 
  qed.
    
  hint simplify map2_pack'R @0, map2_to_list @1.

  lemma andb'SE (w1 w2:WB.t) i :
    (WB.andw w1 w2) \bits'S i = WS.andw (w1 \bits'S i) (w2 \bits'S i).
  proof.
    apply WS.wordP => j hj.
    by rewrite bits'SiE // WB.andwE WS.andwE !bits'SiE.
  qed.

  lemma orb'SE (w1 w2:WB.t) i :
    (WB.orw w1 w2) \bits'S i = WS.orw (w1 \bits'S i) (w2 \bits'S i).
  proof.
    apply WS.wordP => j hj.
    by rewrite bits'SiE // WB.orwE WS.orwE !bits'SiE.
  qed.

  lemma xorb'SE (w1 w2:WB.t) i :
    (WB.(+^) w1 w2) \bits'S i = WS.(+^) (w1 \bits'S i) (w2 \bits'S i).
  proof.
    apply WS.wordP => j hj.
    by rewrite bits'SiE // WB.xorwE WS.xorwE !bits'SiE.
  qed.

  lemma invw'SE (w:WB.t) i :
    0 <= i < r =>
    (WB.invw w) \bits'S i = WS.invw (w \bits'S i).
  proof.
    move=> hi;apply WS.wordP => j hj.
    rewrite bits'SiE // WB.invwE WS.invwE !bits'SiE //.
    by rewrite in_bound /#.
  qed.

  lemma andb'Ru'SE ws1 ws2 :
    WB.andw (pack'R_t ws1) (pack'R_t ws2) = pack'R_t (map2 WS.andw ws1 ws2).
   proof.
     apply (canRL _ _ _ _ unpack'SK); apply packP => i hi.
     by rewrite get_unpack'S // map2iE // andb'SE // !pack'RbE.
   qed.

   lemma orb'Ru'SE ws1 ws2 :
     WB.orw (pack'R_t ws1) (pack'R_t ws2) = pack'R_t (map2 WS.orw ws1 ws2).
   proof.
     apply (canRL _ _ _ _ unpack'SK); apply packP => i hi.
     by rewrite get_unpack'S // map2iE // orb'SE // !pack'RbE.
   qed.

   lemma xorb'Ru'SE ws1 ws2 :
     WB.(+^) (pack'R_t ws1) (pack'R_t ws2) = pack'R_t (map2 WS.(+^) ws1 ws2).
   proof.
     apply (canRL _ _ _ _ unpack'SK); apply packP => i hi.
     by rewrite get_unpack'S // map2iE // xorb'SE // !pack'RbE.
   qed.

   lemma invw'Ru'SE ws :
     WB.invw (pack'R_t ws) = pack'R_t (map WS.invw ws).
   proof.
     apply (canRL _ _ _ _ unpack'SK); apply packP => i hi.
     by rewrite get_unpack'S // mapiE // invw'SE // !pack'RbE.
   qed.

   lemma bits'S_div (w:WB.t) i : 0 <= i =>
     w \bits'S i = WS.of_int (WB.to_uint w %/ (2^(sizeS*i))).
   proof.
     move=> hi;apply WS.to_uintRL;rewrite -bits_divmod.
     + smt (WS.gt0_size). smt (WS.gt0_size).
     rewrite to_uint_bits; congr; rewrite WS.bitsE WB.bitsE; apply eq_in_mkseq.
     by move=> k hk /=;rewrite bits'SiE 1:// mulzC.
   qed.

   lemma of_int_bits'S_div w i : 0 <= i < r =>
     (WB.of_int w) \bits'S i = WS.of_int (w %/ (2^(sizeS*i))).
   proof.
     move=> [h0i hir];rewrite bits'S_div //.
     rewrite WB.of_uintK modz_pow2_div.
     + by rewrite sizeBrS mulzC; apply cmpW; apply mulz_cmp_r.
     rewrite -WS.of_int_mod modz_mod_pow2 !ger0_norm /min; 1,2: smt (sizeBrS WS.gt0_size).
     have -> /= : !sizeB - sizeS * i < sizeS.
     + rewrite sizeBrS.
       have -> : r * sizeS - sizeS * i = sizeS * (r - i) by ring.
       by rewrite -lezNgt;apply ler_pemulr;[ apply ltzW | smt ()].
     by rewrite WS.of_int_mod.
   qed.

   lemma of_int_bits'S_div_red (w i:int) : 0 <= i < r =>
     0 <= `|w| => (* Do not remove this condition, it is used to block reduction *)
     (WB.of_int w) \bits'S i = WS.of_int (w %/ (2^(sizeS*i))).
   proof. by move=> hi hw;apply of_int_bits'S_div. qed.

   hint simplify (pack'RwE, bits'SiE, pack'RbE, get_unpack'S, unpack'SK, pack'RK,
                  mapbE, map2bE, andb'SE, orb'SE, xorb'SE, invw'SE,
                  andb'Ru'SE, orb'Ru'SE, xorb'Ru'SE, invw'Ru'SE, of_int_bits'S_div_red).

   lemma to_uint_zeroextu'B (w:WS.t) :
     WB.to_uint (zeroextu'B w) = WS.to_uint w.
   proof.
     rewrite /zeroextu'B WB.of_uintK modz_small //.
     apply bound_abs;have [h1 h2] := WS.to_uint_cmp w;split => // ?.
     apply: (ltr_le_trans (2^sizeS)) => //.
     smt (ler_weexpn2l le_size WS.gt0_size).
   qed.

  lemma nosmt zeroextu'BE (x: WS.t) :
     zeroextu'B x = pack'R_t (Pack.init (fun i => if i = 0 then x else WS.of_int 0)).
  proof.
     apply/wordP => i h.
     rewrite pack'RbE // of_int_bits'S_div // initE h /=.
     move/mem_range: h.
     rewrite range_ltn; first exact: gt0_r.
     case.
     + by move => ->; rewrite /= to_uintK.
     rewrite /= => /mem_range h.
     have -> /= : i <> 0; first smt().
     rewrite divz_small; last by [].
     have [-> /= /ltr_le_trans ] := WS.to_uint_cmp x.
     apply.
     apply: (ler_trans (2 ^ (sizeS * i))); last exact: ler_norm.
     apply: ler_weexpn2l; first by [].
     smt(WS.gt0_size).
 qed.

   lemma zeroextu'B_bit (w:WS.t) i: (zeroextu'B w).[i] = ((0 <= i < sizeS) /\ w.[i]).
   proof.
     rewrite /zeroextu'B WB.of_intwE /WB.int_bit (modz_small (to_uint w)).
     + smt(gt0_r WS.gt0_size sizeBrS ler_weexpn2l WS.to_uint_cmp).
     have -> := WS.get_to_uint w i.
     case: (0 <= i < sizeS) => hi /=;1: smt(gt0_r WS.gt0_size sizeBrS).
     have [ /#| h]: (i < 0 \/ sizeS <= i) by smt().
     rewrite divz_small 2://.
     smt(gt0_r WS.gt0_size sizeBrS ler_weexpn2l WS.to_uint_cmp).
   qed.

   lemma to_uint_truncateu'S (w:WB.t) :
     WS.to_uint (truncateu'S w) = WB.to_uint w %% 2 ^ sizeS.
   proof. by rewrite /truncateu'S WS.of_uintK. qed.

   lemma zeroext_truncateu'S_and (w:WB.t) :
     zeroextu'B (truncateu'S w) = andw w (WB.of_int (2^sizeS - 1)).
   proof.
     rewrite WB.and_mod; 1: smt (le_size WS.gt0_size).
     rewrite -(WB.to_uintK (zeroextu'B (truncateu'S w))).
     by rewrite to_uint_zeroextu'B to_uint_truncateu'S.
   qed.

   lemma of_uint_pack'R i :
      (WB.of_int i) =
        pack'R (map (fun k => WS.of_int ((i %/ 2^(sizeS * k)) %% 2^sizeS)) (iota_ 0 r)).
   proof.
     rewrite -(unpack'SK (WB.of_int i)) unpack'SE Pack.init_of_list.
     do 2! congr; apply (eq_from_nth (WS.of_int 0)) => [ | k]; rewrite !size_map //.
     move=> hk;rewrite !(nth_map 0) //=.
     move: hk;rewrite size_iota /max gt0_r /= => hk;rewrite !nth_iota //=.
     case: hk => hk1 hk2;rewrite bits'S_div //.
     rewrite WB.of_uintK -(WS.of_int_mod (i %% 2 ^ sizeB %/ 2 ^ (sizeS * k))).
     congr;rewrite modz_pow2_div 1://.
     + by rewrite sizeBrS; smt (WS.gt0_size).
     rewrite modz_dvd 2://;apply dvdz_exp2l.
     rewrite sizeBrS (_: r * sizeS - sizeS * k = sizeS * (r - k)); 1: by ring.
     split; 1: smt (WS.gt0_size).
     by move=> ?;apply ler_pemulr => // /#.
   qed.

   op VPADD_'Ru'S (w1 : WB.t) (w2 : WB.t) =
     map2 WS.(+) w1 w2.

   op VPSUB_'Ru'S (w1 : WB.t) (w2 : WB.t) =
     map2 (fun (x y:WS.t) => x + (- y)) w1 w2. 

   op VPMULL_'Ru'S (w1 : WB.t) (w2 : WB.t) =
     map2 WS.( * ) w1 w2. 
   
   op VPMULH_'Ru'S (w1 : WB.t) (w2 : WB.t) =
     map2 (fun (x y:WS.t) => wmulhs x y) w1 w2.

   op VPSLL_'Ru'S (w : WB.t) (cnt : W8.t) =
     map (fun (w:WS.t) => w `<<` cnt) w.

   op VPSRL_'Ru'S (w : WB.t) (cnt : W8.t) =
     map (fun (w:WS.t) => w `>>` cnt) w.

   op VPSRA_'Ru'S (w : WB.t) (cnt : W8.t) =
     map (fun (w:WS.t) => w `|>>` cnt) w.

   op VPBROADCAST_'Ru'S (w : WS.t) =
     pack'R (map (fun i => w) (iota_ 0 r)).

   op wcmp (cmp: int -> int -> bool) (x y: WS.t) : WS.t =
     if cmp (to_sint x) (to_sint y) then (WS.of_int (-1)) else (WS.of_int 0).

   op VPCMPGT_'Ru'S (w1 : WB.t) (w2: WB.t) =
     map2 (wcmp Int.(<=)) w2 w1.

   op VPCMPEQ_'Ru'S (w1 : WB.t) (w2: WB.t) =
     map2 (wcmp (=)) w1 w2.

   op VPMAXU_'Ru'S (w1 : WB.t) (w2 : WB.t) = 
     map2 (fun x y => if WS.to_uint x < WS.to_uint y then y else x) w1 w2.
  
   op VPMAXS_'Ru'S (w1 : WB.t) (w2 : WB.t) = 
     map2 (fun x y => if WS.to_sint x < WS.to_sint y then y else x) w1 w2.
  
   op VPMINU_'Ru'S (w1 : WB.t) (w2 : WB.t) = 
     map2 (fun x y => if WS.to_uint x < WS.to_uint y then x else y) w1 w2.

   op VPMINS_'Ru'S (w1 : WB.t) (w2 : WB.t) = 
     map2 (fun x y => if WS.to_sint x < WS.to_sint y then x else y) w1 w2.

   op VPEXTR_'S (w: WB.t) (i: W8.t) = w \bits'S ((W8.to_uint i)%% r).

   op VPINSR_'Ru'S (w1:WB.t) (w2:WS.t) (i:W8.t) : WB.t = 
     pack'R_t (init (fun j => if j = to_uint i %% r then w2 else w1 \bits'S j)).

   op VPSLLV_'Ru'S (w1:WB.t) (w2:WB.t) =
     let sll = fun (x1 x2:WS.t) => x1 `<<<` WS.to_uint x2 in
     map2 sll w1 w2.

   op VPSRLV_'Ru'S (w1:WB.t) (w2:WB.t) =
     let srl = fun (x1 x2:WS.t) => x1 `>>>` WS.to_uint x2 in
     map2 srl w1 w2.

   (** TODO CHECKME : still x86 **)
   lemma x86_'Ru'S_rol_xor i w : 0 < i < sizeS =>
      VPSLL_'Ru'S w (W8.of_int i) +^ VPSRL_'Ru'S w (W8.of_int (sizeS - i)) =
      map (fun w0 => WS.rol w0 i) w.
   proof.
     move=> hr;rewrite /VPSRL_'Ru'S /VPSLL_'Ru'S.
     apply wordP => j hj.
     by rewrite xorb'SE !mapbE 1..3:// /= rol_xor_shft.
   qed.

   (** TODO CHECKME : still x86 **)
   lemma x86_'Ru'S_rol_xor_red w1 w2 i si:
     w1 = w2 => W8.to_uint si = sizeS - W8.to_uint i => 0 < W8.to_uint i < sizeS =>
     VPSLL_'Ru'S w1 i +^ VPSRL_'Ru'S w2 si =
     map (fun w0 => WS.rol w0 (W8.to_uint i)) w1.
   proof.
     by move=> -> hsi hi; rewrite -(W8.to_uintK i) -(W8.to_uintK si) hsi x86_'Ru'S_rol_xor.
   qed.

   (** TODO CHECKME : same **)
   hint simplify x86_'Ru'S_rol_xor_red.

end W_WS.

abstract theory BitWordSH.
  op size : int.
  axiom size_le_256 : size <= 256.
  clone include BitWord with op size <- size.

  op shift_mask i = 
    W8.to_uint i %% (if size <= 32 then 32 else size).

  op (`>>`) (w1 : t) (w2 : W8.t) = w1 `>>>` (to_uint w2 %% size).
  op (`<<`) (w1 : t) (w2 : W8.t) = w1 `<<<` (to_uint w2 %% size).
  op (`|>>`) (w1 : t) (w2 : W8.t) = sar w1 (to_uint w2 %% size).
  op (`|>>|`) (w1 : t) (w2 : W8.t) = w1 `|>>>|` (to_uint w2 %% size).
  op (`|<<|`) (w1 : t) (w2 : W8.t) = w1 `|<<<|` (to_uint w2 %% size).

  lemma shr_div w1 w2 : to_uint (w1 `>>` w2) = to_uint w1 %/ 2^ (to_uint w2 %% size).
  proof.
    rewrite -{1}(to_uintK w1) /(`>>`) shrDP; 1: smt (modz_cmp gt0_size).
    rewrite of_uintK to_uint_mod modz_small 2://.
    apply bound_abs; apply divz_cmp; 1: by apply gt0_pow2.
    by have:= to_uint_cmp w1; smt (gt0_pow2).
  qed.

  lemma shr_div_le w1 i : 0 <= i < size =>
     to_uint (w1 `>>` (W8.of_int i)) = to_uint w1 %/ 2^ i.
  proof.
    move=> hi;rewrite shr_div of_uintK.
    rewrite (modz_small i) 1:pow2_8; 1: smt (size_le_256).
    by rewrite modz_small //;apply bound_abs.
  qed.

  lemma rol_xor_shft w i : 0 < i < size =>
    w `|<<<|` i = (w `<<` W8.of_int i) +^ (w `>>` W8.of_int (size - i)).
  proof.
    move=> hi; rewrite /(`<<`) /(`>>`) !W8.of_uintK.
    have h : 0 <= i < `|W8.modulus|.
    + by rewrite /=; smt (size_le_256).
    rewrite !(modz_small _ W8.modulus) 1:// 1: #smt: (size_le_256) !modz_small 1,2:/#.
    by rewrite rol_xor 1:/#.
  qed.

  lemma shl_shlw k w:
   0 <= k < size =>
   w `<<` W8.of_int k = w `<<<` k.
  proof.
   move=> *; rewrite /(`<<`) of_uintK (modz_small (k %% W8.modulus)).
    smt(modz_cmp).
   by rewrite modz_small //; smt(size_le_256).
  qed.

  lemma shr_shrw k w:
   0 <= k < size =>
   w `>>` W8.of_int k = w `>>>` k.
  proof.
   move=> *; rewrite /(`>>`) of_uintK (modz_small (k %% W8.modulus)).
    smt(modz_cmp).
   by rewrite modz_small //; smt(size_le_256).
  qed.

  theory SHIFT.
  
  op ROR_XX (v: t) (i: W8.t) =
    let i = shift_mask i in
    if i = 0 then (undefined_flag, undefined_flag, v) 
    else
      let r = v `|>>>|` i in
      let CF = ALU.SF_of r in
      let OF = if i = 1 then CF <> ALU.SF_of v else undefined_flag in
      (OF , CF,  r)
  axiomatized by ROR_XX_E.
  
  op ROL_XX (v: t) (i: W8.t) =
    let i = shift_mask i in
    if i = 0 then(undefined_flag, undefined_flag, v)
    else
      let r = v `|<<<|` i in
      let CF = lsb r in
      let OF = if i = 1 then ALU.SF_of r <> CF else undefined_flag in
      (OF, CF, r)
  axiomatized by ROL_XX_E.
  
  op im i = 
    if size = 8 then i %% 9
    else if size = 16 then i %% 17
    else i.

  op RCL_XX (v: t) (i: W8.t) (cf:bool) =
    let i  = shift_mask i in
    let i = im i in
    let r  = fun j => if j = 0 then cf else v.[j-1] in
    let r  = fun j => r ((j - i) %% (size + 1)) in
    let CF = r 0 in 
    let r  = init (fun j => r (j+1)) in
    let OF = if i = 1 then (ALU.SF_of r <> CF) else undefined_flag in
    (OF, CF, r).
  
  op RCR_XX (v: t) (i: W8.t) (cf:bool) =
    let i  = shift_mask i in
    let i = im i in
    let r  = fun j => if j = 0 then cf else v.[j-1] in
    let r  = fun j => r ((j + i) %% (size + 1)) in
    let OF = if i = 1 then ALU.SF_of  v <> cf else undefined_flag in
    let CF = r 0 in 
    let r  = init (fun j => r (j+1)) in
    (OF, CF, r).

  op rflags_OF (i:int) (r:t) (rc OF:bool) =
    let OF = if i = 1 then OF else undefined_flag in
    let CF = rc in
    let SF = ALU.SF_of r in
    let PF = lsb r in
    let ZF = ALU.ZF_of r in
    (OF, CF, SF, PF, ZF, r).

  op SHL_XX  (v: t) (i: W8.t) =
    let i = shift_mask i in
    if i = 0 then flags_w rflags_undefined v
    else
      let rc = ALU.SF_of (v `<<<` (i - 1)) in 
      let r  = v `<<<` i in
      rflags_OF i r rc (ALU.SF_of r ^^ rc).

  abbrev [-printing] SAL_XX = SHL_XX.

  op SHLD_XX (v1 v2: t) (i: W8.t) =
    let i = shift_mask i in
    if i = 0 then flags_w rflags_undefined v1
    else
      let rc = ALU.SF_of (v1 `<<<` (i - 1)) in
      let r1 = v1 `<<<` i in
      let r2 = v2 `>>>` (size - i) in
      let r  = r1 +^ r2 in
      rflags_OF i r rc (ALU.SF_of r ^^ rc).
  
  op SHR_XX (v: t) (i: W8.t) =
    let i = shift_mask i in 
    if i = 0 then flags_w rflags_undefined v 
    else
      let rc = lsb (v `>>>` i -1) in
      let r  = v `>>>` i in
      rflags_OF i r rc (ALU.SF_of r).
  
  op SHRD_XX (v1 v2: t) (i: W8.t) = 
    let i = shift_mask i in
    if i = 0 then flags_w rflags_undefined v1
    else
      let rc = lsb (v1 `>>>` i - 1) in
      let r1 = v1 `>>>` i in
      let r2 = v2 `<<<` (size - i) in
      let r  = r1 +^ r2 in
      rflags_OF i r rc (ALU.SF_of r ^^ ALU.SF_of v1).
  
  op SAR_XX (v: t) (i: W8.t) = 
    let i = shift_mask i in 
    if i = 0 then flags_w rflags_undefined v
    else
      let rc = lsb (sar v (i - 1)) in
      let r  = sar v i in
      rflags_OF i r rc false.

end SHIFT.
  
end BitWordSH.

theory W16.
  abbrev [-printing] size = 16.
  clone include BitWordSH with op size <- size
  rename "_XX" as "_16"
  proof gt0_size by done,
        size_le_256 by done.

end W16. export W16 W16.ALU W16.SHIFT.

clone export W_WS as W2u8 with
  op sizeS <- W8.size, op sizeB <- W16.size, op r <- 2,
  theory WS <- W8, theory WB <- W16
  proof gt0_r by done, sizeBrS by done
  rename [op, lemma] "'Ru'S" as "2u8" "'R" as "2" "'S" as "8" "'B" as "16" .

theory W32.
  abbrev [-printing] size = 32.
  clone include BitWordSH with op size <- size
  rename "_XX" as "_32"
  proof gt0_size by done,
        size_le_256 by done.
end W32. export W32 W32.ALU W32.SHIFT.

clone export W_WS as W4u8 with
  op sizeS <- W8.size, op sizeB <- W32.size, op r <- 4,
  theory WS <- W8, theory WB <- W32
  proof gt0_r by done, sizeBrS by done
  rename [op, lemma] "'Ru'S" as "4u8" "'R" as "4" "'S" as "8" "'B" as "32".

clone export W_WS as W2u16 with
  op sizeS <- W16.size, op sizeB <- W32.size, op r <- 2,
  theory WS <- W16, theory WB <- W32
  proof gt0_r by done, sizeBrS by done
  rename [op, lemma] "'Ru'S" as "2u16" "'R" as "2" "'S" as "16" "'B" as "32".

theory W64.
  abbrev [-printing] size = 64.
  clone include BitWordSH with op size <- size
  rename "_XX" as "_64"
  proof gt0_size by done,
        size_le_256 by done.
end W64. export W64 W64.ALU W64.SHIFT.

clone export W_WS as W8u8 with
  op sizeS <- W8.size, op sizeB <- W64.size, op r <- 8,
  theory WS <- W8, theory WB <- W64
  proof gt0_r by done, sizeBrS by done
  rename [op, lemma] "'Ru'S" as "8u8" "'R" as "8" "'S" as "8" "'B" as "64".

clone export W_WS as W4u16 with
  op sizeS <- W16.size, op sizeB <- W64.size, op r <- 4,
  theory WS <- W16, theory WB <- W64
  proof gt0_r by done, sizeBrS by done
  rename [op, lemma] "'Ru'S" as "4u16" "'R" as "4" "'S" as "16" "'B" as "64".

clone export W_WS as W2u32 with
  op sizeS <- W32.size, op sizeB <- W64.size, op r <- 2,
  theory WS <- W32, theory WB <- W64
  proof gt0_r by done, sizeBrS by done
  rename [op, lemma] "'Ru'S" as "2u32" "'R" as "2" "'S" as "32" "'B" as "64".

theory W128.
  abbrev [-printing] size = 128.
  clone include BitWordSH with op size <- size
  rename "_XX" as "_128"
  proof gt0_size by done,
        size_le_256 by done.
end W128. export W128 W128.ALU W128.SHIFT.

clone export W_WS as W16u8 with
  op sizeS <- W8.size, op sizeB <- W128.size, op r <- 16,
  theory WS <- W8, theory WB <- W128
  proof gt0_r by done, sizeBrS by done
  rename [op, lemma] "'Ru'S" as "16u8" "'R" as "16" "'S" as "8" "'B" as "128".

clone export W_WS as W8u16 with
  op sizeS <- W16.size, op sizeB <- W128.size, op r <- 8,
  theory WS <- W16, theory WB <- W128
  proof gt0_r by done, sizeBrS by done
  rename [op, lemma] "'Ru'S" as "8u16" "'R" as "8" "'S" as "16" "'B" as "128".

clone export W_WS as W4u32 with
  op sizeS <- W32.size, op sizeB <- W128.size, op r <- 4,
  theory WS <- W32, theory WB <- W128
  proof gt0_r by done, sizeBrS by done
  rename [op, lemma] "'Ru'S" as "4u32" "'R" as "4" "'S" as "32" "'B" as "128".

clone export W_WS as W2u64 with
  op sizeS <- W64.size, op sizeB <- W128.size, op r <- 2,
  theory WS <- W64, theory WB <- W128
  proof gt0_r by done, sizeBrS by done
  rename [op, lemma] "'Ru'S" as "2u64" "'R" as "2" "'S" as "64" "'B" as "128".

theory W256.
  abbrev [-printing] size = 256.
  clone include BitWordSH with op size <- size
  rename "_XX" as "_256"
  proof gt0_size by done,
        size_le_256 by done.
end W256. export W256 W256.ALU W256.SHIFT.

clone export W_WS as W32u8 with
  op sizeS <- W8.size, op sizeB <- W256.size, op r <- 32,
  theory WS <- W8, theory WB <- W256
  proof gt0_r by done, sizeBrS by done
  rename [op, lemma] "'Ru'S" as "32u8" "'R" as "32" "'S" as "8" "'B" as "256".

clone export W_WS as W16u16 with
  op sizeS <- W16.size, op sizeB <- W256.size, op r <- 16,
  theory WS <- W16, theory WB <- W256
  proof gt0_r by done, sizeBrS by done
  rename [op, lemma] "'Ru'S" as "16u16" "'R" as "16" "'S" as "16" "'B" as "256".

clone export W_WS as W8u32 with
  op sizeS <- W32.size, op sizeB <- W256.size, op r <- 8,
  theory WS <- W32, theory WB <- W256
  proof gt0_r by done, sizeBrS by done
  rename [op, lemma] "'Ru'S" as "8u32" "'R" as "8" "'S" as "32" "'B" as "256".

clone export W_WS as W4u64 with
  op sizeS <- W64.size, op sizeB <- W256.size, op r <- 4,
  theory WS <- W64, theory WB <- W256
  proof gt0_r by done, sizeBrS by done
  rename [op, lemma] "'Ru'S" as "4u64" "'R" as "4" "'S" as "64" "'B" as "256".

clone export W_WS as W2u128 with
  op sizeS <- W128.size, op sizeB <- W256.size, op r <- 2,
  theory WS <- W128, theory WB <- W256
  proof gt0_r by done, sizeBrS by done
  rename [op, lemma] "'Ru'S" as "2u128" "'R" as "2" "'S" as "128" "'B" as "256".


(* -------------------------------------------------------------------- *)
(* Word size                                                            *)

type wsize = [
  | W8
  | W16
  | W32
  | W64
  | W128
  | W256
].

op wsize_i (w : wsize) =
  with w = W8   => 1
  with w = W16  => 2
  with w = W32  => 4
  with w = W64  => 8
  with w = W128 => 16
  with w = W256 => 32.

(* TODO move *)
lemma gt0_wsize_i ws: 0 < wsize_i ws.
proof. by case ws. qed.
hint exact : gt0_wsize_i.

lemma div_le_wsize ws1 ws2 : wsize_i ws1 <= wsize_i ws2 => wsize_i ws1 %| wsize_i ws2.
proof. by case: ws1 ws2 => -[]. qed.

lemma div_wsize_modulus ws : wsize_i ws %| W64.modulus.
proof. by case ws. qed.
hint exact : div_wsize_modulus.

lemma divmod_mul n d i j :
  0 < n =>
  0 <= j < d =>
  (i * d + j) %/ (n * d) = i%/ n /\ (i * d + j) %% (n * d) = i %% n * d + j.
proof.
  move=> hn hj.
  have -> : i * d + j = (i %/ n) * (n * d) + (d * (i %% n) + j).
  + have [h1 h2]:= edivzP i n.
    by rewrite {1 2} h1 divzMDl 1:/# (divz_small (i%%n) n) 1:/# /=; ring.
  rewrite divzMDl 1:/# modzMDl.
  have hb: 0 <= d * (i %% n) + j < `|n * d|.
  + have := modz_cmp i n hn.
    have -> : `|n * d| = n * d by smt().
    have -> h : n * d = (n-1) * d + d by ring.
    split;1: smt(); move=> ?.
    apply ler_lt_add; 2:smt().
    by rewrite mulzC ler_pmul2r /#.
  by rewrite (divz_small _ (n*d)) 1://  (modz_small _ (n*d)) 1:// /=; ring.
qed.

(* --------------------------------------------------------------------------------- *)
(* Lemmas on \bits8                                                                  *)
(* --------------------------------------------------------------------------------- *)

lemma bits8_W2u16 ws i :
  W2u16.pack2_t ws \bits8 i = if 0 <= i < 4 then ws.[i%/2] \bits8 (i%%2) else W8.zero.
proof.
  apply W8.wordP => j hj; rewrite !bits8iE 1,2://.
  case: (0 <= i < 4) => /= hi; last by rewrite W32.get_out 1:/#.
  rewrite pack2wE 1:/#; have /= [-> ->] := divmod_mul 2 8 i j _ hj; 1 :done; rewrite W2u8.bits8iE 1:// /#.
qed.

lemma bits8_W2u16_red ws i :
  0 <= i < 4 => W2u16.pack2_t ws \bits8 i = ws.[i%/2] \bits8 (i%%2).
proof. by move=> h;rewrite bits8_W2u16 h. qed.

lemma bits8_W4u16 ws i :
  W4u16.pack4_t ws \bits8 i = if 0 <= i < 8 then ws.[i%/2] \bits8 (i%%2) else W8.zero.
proof.
  apply W8.wordP => j hj; rewrite !bits8iE 1,2://.
  case: (0 <= i < 8) => /= hi; last by rewrite W64.get_out 1:/#.
  rewrite pack4wE 1:/#; have /= [-> ->] := divmod_mul 2 8 i j _ hj; 1:done; rewrite W2u8.bits8iE 1:// /#.
qed.

lemma bits8_W4u16_red ws i :
  0 <= i < 8 => W4u16.pack4_t ws \bits8 i = ws.[i%/2] \bits8 (i%%2).
proof. by move=> h;rewrite bits8_W4u16 h. qed.

lemma bits8_W8u16 ws i :
  W8u16.pack8_t ws \bits8 i = if 0 <= i < 16 then ws.[i%/2] \bits8 (i%%2) else W8.zero.
proof.
  apply W8.wordP => j hj; rewrite !bits8iE 1,2://.
  case: (0 <= i < 16) => /= hi; last by rewrite W128.get_out 1:/#.
  rewrite pack8wE 1:/#; have [-> ->] := divmod_mul 2 8 i j _ hj; 1: done; rewrite W2u8.bits8iE 1:// /#.
qed.

lemma bits8_W8u16_red ws i :
  0 <= i < 16 => W8u16.pack8_t ws \bits8 i = ws.[i%/2] \bits8 (i%%2).
proof. by move=> h;rewrite bits8_W8u16 h. qed.

lemma bits8_W16u16 ws i :
  W16u16.pack16_t ws \bits8 i = if 0 <= i < 32 then ws.[i%/2] \bits8 (i%%2) else W8.zero.
proof.
  apply W8.wordP => j hj; rewrite !bits8iE 1,2://.
  case: (0 <= i < 32) => /= hi; last by rewrite W256.get_out 1:/#.
  rewrite pack16wE 1:/#; have [-> ->] := divmod_mul 2 8 i j _ hj; 1: done; rewrite W2u8.bits8iE 1:// /#.
qed.

lemma bits8_W16u16_red ws i :
  0 <= i < 32 => W16u16.pack16_t ws \bits8 i = ws.[i%/2] \bits8 (i%%2).
proof. by move=> h;rewrite bits8_W16u16 h. qed.

hint simplify bits8_W2u16_red, bits8_W4u16_red, bits8_W8u16_red, bits8_W16u16_red.

lemma bits8_W2u32 ws i :
  W2u32.pack2_t ws \bits8 i = if 0 <= i < 8 then ws.[i%/4] \bits8 (i%%4) else W8.zero.
proof.
  apply W8.wordP => j hj; rewrite !bits8iE 1,2://.
  case: (0 <= i < 8) => /= hi; last by rewrite W64.get_out 1:/#.
  rewrite pack2wE 1:/#; have /= [-> ->] := divmod_mul 4 8 i j _ hj; 1: done; rewrite W4u8.bits8iE 1:// /#.
qed.

lemma bits8_W2u32_red ws i :
  0 <= i < 8 => W2u32.pack2_t ws \bits8 i = ws.[i%/4] \bits8 (i%%4).
proof. by move=> h;rewrite bits8_W2u32 h. qed.

lemma bits8_W4u32 ws i :
  W4u32.pack4_t ws \bits8 i = if 0 <= i < 16 then ws.[i%/4] \bits8 (i%%4) else W8.zero.
proof.
  apply W8.wordP => j hj; rewrite !bits8iE 1,2://.
  case: (0 <= i < 16) => /= hi; last by rewrite W128.get_out 1:/#.
  rewrite pack4wE 1:/#; have /= [-> ->] := divmod_mul 4 8 i j _ hj; 1: done; rewrite W4u8.bits8iE 1:// /#.
qed.

lemma bits8_W4u32_red ws i :
  0 <= i < 16 => W4u32.pack4_t ws \bits8 i = ws.[i%/4] \bits8 (i%%4).
proof. by move=> h;rewrite bits8_W4u32 h. qed.

lemma bits8_W8u32 ws i :
  W8u32.pack8_t ws \bits8 i = if 0 <= i < 32 then ws.[i%/4] \bits8 (i%%4) else W8.zero.
proof.
  apply W8.wordP => j hj; rewrite !bits8iE 1,2://.
  case: (0 <= i < 32) => /= hi; last by rewrite W256.get_out 1:/#.
  rewrite pack8wE 1:/#; have /= [-> ->] := divmod_mul 4 8 i j _ hj; 1: done; rewrite W4u8.bits8iE 1:// /#.
qed.

lemma bits8_W8u32_red ws i :
  0 <= i < 32 => W8u32.pack8_t ws \bits8 i = ws.[i%/4] \bits8 (i%%4).
proof. by move=> h;rewrite bits8_W8u32 h. qed.

hint simplify bits8_W2u32_red, bits8_W4u32_red, bits8_W8u32_red.

lemma bits8_W2u64 ws i :
  W2u64.pack2_t ws \bits8 i = if 0 <= i < 16 then ws.[i%/8] \bits8 (i%%8) else W8.zero.
proof.
  apply W8.wordP => j hj; rewrite !bits8iE 1,2://.
  case: (0 <= i < 16) => /= hi; last by rewrite W128.get_out 1:/#.
  rewrite pack2wE 1:/#; have /= [-> ->] := divmod_mul 8 8 i j _ hj; 1: done; rewrite W8u8.bits8iE 1:// /#.
qed.

lemma bits8_W2u64_red ws i :
  0 <= i < 16 => W2u64.pack2_t ws \bits8 i = ws.[i%/8] \bits8 (i%%8).
proof. by move=> h;rewrite bits8_W2u64 h. qed.

lemma bits8_W4u64 ws i :
  W4u64.pack4_t ws \bits8 i = if 0 <= i < 32 then ws.[i%/8] \bits8 (i%%8) else W8.zero.
proof.
  apply W8.wordP => j hj; rewrite !bits8iE 1,2://.
  case: (0 <= i < 32) => /= hi; last by rewrite W256.get_out 1:/#.
  rewrite pack4wE 1:/#; have /= [-> ->] := divmod_mul 8 8 i j _ hj; 1: done; rewrite W8u8.bits8iE 1:// /#.
qed.

lemma bits8_W4u64_red ws i :
  0 <= i < 32 => W4u64.pack4_t ws \bits8 i = ws.[i%/8] \bits8 (i%%8).
proof. by move=> h;rewrite bits8_W4u64 h. qed.

hint simplify bits8_W2u64_red, bits8_W4u64_red.

lemma bits8_W2u128 ws i :
  W2u128.pack2_t ws \bits8 i = if 0 <= i < 32 then ws.[i%/16] \bits8 (i%%16) else W8.zero.
proof.
  apply W8.wordP => j hj; rewrite !bits8iE 1,2://.
  case: (0 <= i < 32) => /= hi; last by rewrite W256.get_out 1:/#.
  rewrite pack2wE 1:/#; have /= [-> ->] := divmod_mul 16 8 i j _ hj; 1: done; rewrite W16u8.bits8iE 1:// /#.
qed.

lemma bits8_W2u128_red ws i :
  0 <= i < 32 => W2u128.pack2_t ws \bits8 i = ws.[i%/16] \bits8 (i%%16).
proof. by move=> h;rewrite bits8_W2u128 h. qed.

hint simplify bits8_W2u128_red.

lemma W32_bits16_bits8 (w:W32.t) i j: 0 <= j < 2 => w \bits16 i \bits8 j = w \bits8 (2 * i + j).
proof.
  move=> hj; apply W8.wordP => k hk.
  by rewrite !bits8iE 1,2:// bits16iE 1:/#; congr; ring.
qed.

lemma W64_bits16_bits8 (w:W64.t) i j: 0 <= j < 2 => w \bits16 i \bits8 j = w \bits8 (2 * i + j).
proof.
  move=> hj; apply W8.wordP => k hk.
  by rewrite !bits8iE 1,2:// bits16iE 1:/#; congr; ring.
qed.

lemma W128_bits16_bits8 (w:W128.t) i j: 0 <= j < 2 => w \bits16 i \bits8 j = w \bits8 (2 * i + j).
proof.
  move=> hj; apply W8.wordP => k hk.
  by rewrite !bits8iE 1,2:// bits16iE 1:/#; congr; ring.
qed.

lemma W256_bits16_bits8 (w:W256.t) i j: 0 <= j < 2 => w \bits16 i \bits8 j = w \bits8 (2 * i + j).
proof.
  move=> hj; apply W8.wordP => k hk.
  by rewrite !bits8iE 1,2:// bits16iE 1:/#; congr; ring.
qed.

hint simplify W32_bits16_bits8, W64_bits16_bits8, W128_bits16_bits8, W256_bits16_bits8.

lemma W64_bits32_bits8 (w:W64.t) i j: 0 <= j < 4 => w \bits32 i \bits8 j = w \bits8 (4 * i + j).
proof.
  move=> hj; apply W8.wordP => k hk.
  by rewrite !bits8iE 1,2:// bits32iE 1:/#; congr; ring.
qed.

lemma W128_bits32_bits8 (w:W128.t) i j: 0 <= j < 4 => w \bits32 i \bits8 j = w \bits8 (4 * i + j).
proof.
  move=> hj; apply W8.wordP => k hk.
  by rewrite !bits8iE 1,2:// bits32iE 1:/#; congr; ring.
qed.

lemma W256_bits32_bits8 (w:W256.t) i j: 0 <= j < 4 => w \bits32 i \bits8 j = w \bits8 (4 * i + j).
proof.
  move=> hj; apply W8.wordP => k hk.
  by rewrite !bits8iE 1,2:// bits32iE 1:/#; congr; ring.
qed.

hint simplify W64_bits32_bits8, W128_bits32_bits8, W256_bits32_bits8.

lemma W128_bits64_bits8 (w:W128.t) i j: 0 <= j < 8 => w \bits64 i \bits8 j = w \bits8 (8 * i + j).
proof.
  move=> hj; apply W8.wordP => k hk.
  by rewrite !bits8iE 1,2:// bits64iE 1:/#; congr; ring.
qed.

lemma W256_bits64_bits8 (w:W256.t) i j: 0 <= j < 8 => w \bits64 i \bits8 j = w \bits8 (8 * i + j).
proof.
  move=> hj; apply W8.wordP => k hk.
  by rewrite !bits8iE 1,2:// bits64iE 1:/#; congr; ring.
qed.

hint simplify W128_bits64_bits8, W256_bits64_bits8.

lemma W256_bits128_bits8 (w:W256.t) i j: 0 <= j < 16 => w \bits128 i \bits8 j = w \bits8 (16 * i + j).
proof.
  move=> hj; apply W8.wordP => k hk.
  by rewrite !bits8iE 1,2:// bits128iE 1:/#; congr; ring.
qed.

hint simplify W256_bits128_bits8.

(* --------------------------------------------------------------------------------- *)
(* Lemmas on \bits16                                                                  *)
(* --------------------------------------------------------------------------------- *)

lemma bits16_W4u8 ws i :
  W4u8.pack4_t ws \bits16 i = if 0 <= i < 2 then W2u8.pack2 [ws.[2 * i]; ws.[2 * i + 1]] else W16.zero.
proof.
  apply W2u8.wordP => j hj.
  rewrite W32_bits16_bits8 1://.
  case: (0 <= i < 2) => hi; last by rewrite W2u8.get_zero W4u8.get_out 1:/#.
  rewrite /= W2u8.pack2bE 1:// /= W4u8.pack4bE 1:/#.
  by have []-> : j = 0 \/ j = 1 by smt().
qed.

lemma bits16_W4u8_red ws i :
  0 <= i < 2 => W4u8.pack4_t ws \bits16 i = W2u8.pack2 [ws.[2 * i]; ws.[2 * i + 1]].
proof. by move=> h;rewrite bits16_W4u8 h. qed.

lemma bits16_W8u8 ws i :
  W8u8.pack8_t ws \bits16 i = if 0 <= i < 4 then W2u8.pack2 [ws.[2 * i]; ws.[2 * i + 1]] else W16.zero.
proof.
  apply W2u8.wordP => j hj.
  rewrite W64_bits16_bits8 1://.
  case: (0 <= i < 4) => hi; last by rewrite W2u8.get_zero W8u8.get_out 1:/#.
  rewrite /= W2u8.pack2bE 1:// /= W8u8.pack8bE 1:/#.
  have []-> //: j = 0 \/ j = 1 by smt().
qed.

lemma bits16_W8u8_red ws i :
  0 <= i < 4 => W8u8.pack8_t ws \bits16 i = W2u8.pack2 [ws.[2 * i]; ws.[2 * i + 1]].
proof. by move=> h;rewrite bits16_W8u8 h. qed.

lemma bits16_W16u8 ws i :
  W16u8.pack16_t ws \bits16 i = if 0 <= i < 8 then W2u8.pack2 [ws.[2 * i]; ws.[2 * i + 1]] else W16.zero.
proof.
  apply W2u8.wordP => j hj.
  rewrite W128_bits16_bits8 1://.
  case: (0 <= i < 8) => hi; last by rewrite W2u8.get_zero W16u8.get_out 1:/#.
  rewrite /= W2u8.pack2bE 1:// /= W16u8.pack16bE 1:/#.
  have []-> //: j = 0 \/ j = 1 by smt().
qed.

lemma bits16_W16u8_red ws i :
  0 <= i < 8 => W16u8.pack16_t ws \bits16 i = W2u8.pack2 [ws.[2 * i]; ws.[2 * i + 1]].
proof. by move=> h;rewrite bits16_W16u8 h. qed.

lemma bits16_W32u8 ws i :
  W32u8.pack32_t ws \bits16 i = if 0 <= i < 16 then W2u8.pack2 [ws.[2 * i]; ws.[2 * i + 1]] else W16.zero.
proof.
  apply W2u8.wordP => j hj.
  rewrite W256_bits16_bits8 1://.
  case: (0 <= i < 16) => hi; last by rewrite W2u8.get_zero W32u8.get_out 1:/#.
  rewrite /= W2u8.pack2bE 1:// /= W32u8.pack32bE 1:/#.
  have []-> //: j = 0 \/ j = 1 by smt().
qed.

lemma bits16_W32u8_red ws i :
  0 <= i < 16 => W32u8.pack32_t ws \bits16 i = W2u8.pack2 [ws.[2 * i]; ws.[2 * i + 1]].
proof. by move=> h;rewrite bits16_W32u8 h. qed.

hint simplify bits16_W4u8_red, bits16_W8u8_red, bits16_W16u8_red, bits16_W32u8.

lemma bits16_W2u32 ws i :
  W2u32.pack2_t ws \bits16 i = if 0 <= i < 4 then ws.[i%/2] \bits16 (i%%2) else W16.zero.
proof.
  apply W16.wordP => j hj; rewrite !bits16iE 1,2://.
  case: (0 <= i < 4) => /= hi; last by rewrite W64.get_out 1:/#.
  rewrite pack2wE 1:/#; have /= [-> ->] := divmod_mul 2 16 i j _ hj; 1: done; rewrite W2u16.bits16iE 1:// /#.
qed.

lemma bits16_W2u32_red ws i :
  0 <= i < 4 => W2u32.pack2_t ws \bits16 i = ws.[i%/2] \bits16 (i%%2).
proof. by move=> h;rewrite bits16_W2u32 h. qed.

lemma bits16_W4u32 ws i :
  W4u32.pack4_t ws \bits16 i = if 0 <= i < 8 then ws.[i%/2] \bits16 (i%%2) else W16.zero.
proof.
  apply W16.wordP => j hj; rewrite !bits16iE 1,2://.
  case: (0 <= i < 8) => /= hi; last by rewrite W128.get_out 1:/#.
  rewrite pack4wE 1:/#; have /= [-> ->] := divmod_mul 2 16 i j _ hj; 1: done; rewrite W2u16.bits16iE 1:// /#.
qed.

lemma bits16_W4u32_red ws i :
  0 <= i < 8 => W4u32.pack4_t ws \bits16 i = ws.[i%/2] \bits16 (i%%2).
proof. by move=> h;rewrite bits16_W4u32 h. qed.

lemma bits16_W8u32 ws i :
  W8u32.pack8_t ws \bits16 i = if 0 <= i < 16 then ws.[i%/2] \bits16 (i%%2) else W16.zero.
proof.
  apply W16.wordP => j hj; rewrite !bits16iE 1,2://.
  case: (0 <= i < 16) => /= hi; last by rewrite W256.get_out 1:/#.
  rewrite pack8wE 1:/#; have /= [-> ->] := divmod_mul 2 16 i j _ hj; 1: done; rewrite W2u16.bits16iE 1:// /#.
qed.

lemma bits16_W8u32_red ws i :
  0 <= i < 16 => W8u32.pack8_t ws \bits16 i = ws.[i%/2] \bits16 (i%%2).
proof. by move=> h;rewrite bits16_W8u32 h. qed.

hint simplify bits16_W2u32_red, bits16_W4u32_red, bits16_W8u32_red.

lemma bits16_W2u64 ws i :
  W2u64.pack2_t ws \bits16 i = if 0 <= i < 8 then ws.[i%/4] \bits16 (i%%4) else W16.zero.
proof.
  apply W16.wordP => j hj; rewrite !bits16iE 1,2://.
  case: (0 <= i < 8) => /= hi; last by rewrite W128.get_out 1:/#.
  rewrite pack2wE 1:/#; have /= [-> ->] := divmod_mul 4 16 i j _ hj; 1: done; rewrite W4u16.bits16iE 1:// /#.
qed.

lemma bits16_W2u64_red ws i :
  0 <= i < 8 => W2u64.pack2_t ws \bits16 i = ws.[i%/4] \bits16 (i%%4).
proof. by move=> h;rewrite bits16_W2u64 h. qed.

lemma bits16_W4u64 ws i :
  W4u64.pack4_t ws \bits16 i = if 0 <= i < 16 then ws.[i%/4] \bits16 (i%%4) else W16.zero.
proof.
  apply W16.wordP => j hj; rewrite !bits16iE 1,2://.
  case: (0 <= i < 16) => /= hi; last by rewrite W256.get_out 1:/#.
  rewrite pack4wE 1:/#; have /= [-> ->] := divmod_mul 4 16 i j _ hj; 1: done; rewrite W4u16.bits16iE 1:// /#.
qed.

lemma bits16_W4u64_red ws i :
  0 <= i < 16 => W4u64.pack4_t ws \bits16 i = ws.[i%/4] \bits16 (i%%4).
proof. by move=> h;rewrite bits16_W4u64 h. qed.

hint simplify bits16_W2u64_red, bits16_W4u64_red.

lemma bits16_W2u128 ws i :
  W2u128.pack2_t ws \bits16 i = if 0 <= i < 16 then ws.[i%/8] \bits16 (i%%8) else W16.zero.
proof.
  apply W16.wordP => j hj; rewrite !bits16iE 1,2://.
  case: (0 <= i < 16) => /= hi; last by rewrite W256.get_out 1:/#.
  rewrite pack2wE 1:/#; have /= [-> ->] := divmod_mul 8 16 i j _ hj; 1: done; rewrite W8u16.bits16iE 1:// /#.
qed.

lemma bits16_W2u128_red ws i :
  0 <= i < 16 => W2u128.pack2_t ws \bits16 i = ws.[i%/8] \bits16 (i%%8).
proof.  by move=> h;rewrite bits16_W2u128 h. qed.

hint simplify bits16_W2u128_red.

lemma W64_bits32_bits16 (w:W64.t) i j: 0 <= j < 2 => w \bits32 i \bits16 j = w \bits16 (2 * i + j).
proof.
  move=> hj; apply W16.wordP => k hk.
  by rewrite !bits16iE 1,2:// bits32iE 1:/#; congr; ring.
qed.

lemma W128_bits32_bits16 (w:W128.t) i j: 0 <= j < 2 => w \bits32 i \bits16 j = w \bits16 (2 * i + j).
proof.
  move=> hj; apply W16.wordP => k hk.
  by rewrite !bits16iE 1,2:// bits32iE 1:/#; congr; ring.
qed.

lemma W256_bits32_bits16 (w:W256.t) i j: 0 <= j < 2 => w \bits32 i \bits16 j = w \bits16 (2 * i + j).
proof.
  move=> hj; apply W16.wordP => k hk.
  by rewrite !bits16iE 1,2:// bits32iE 1:/#; congr; ring.
qed.

hint simplify W64_bits32_bits16, W128_bits32_bits16, W256_bits32_bits16.

lemma W128_bits64_bits16 (w:W128.t) i j: 0 <= j < 4 => w \bits64 i \bits16 j = w \bits16 (4 * i + j).
proof.
  move=> hj; apply W16.wordP => k hk.
  by rewrite !bits16iE 1,2:// bits64iE 1:/#; congr; ring.
qed.

lemma W256_bits64_bits16 (w:W256.t) i j: 0 <= j < 4 => w \bits64 i \bits16 j = w \bits16 (4 * i + j).
proof.
  move=> hj; apply W16.wordP => k hk.
  by rewrite !bits16iE 1,2:// bits64iE 1:/#; congr; ring.
qed.

lemma W256_bits128_bits16 (w:W256.t) i j: 0 <= j < 8 => w \bits128 i \bits16 j = w \bits16 (8 * i + j).
proof.
  move=> hj; apply W16.wordP => k hk.
  by rewrite !bits16iE 1,2:// bits128iE 1:/#; congr; ring.
qed.

hint simplify W128_bits64_bits16, W256_bits64_bits16, W256_bits128_bits16.

(* --------------------------------------------------------------------------------- *)
(* Lemmas on \bits32                                                                  *)
(* --------------------------------------------------------------------------------- *)

lemma bits32_W8u8 ws i :
  W8u8.pack8_t ws \bits32 i =
    if 0 <= i < 2 then W4u8.pack4 [ws.[4 * i]; ws.[4 * i + 1]; ws.[4 * i + 2]; ws.[4 * i + 3] ] else W32.zero.
proof.
  apply W4u8.wordP => j hj.
  rewrite W64_bits32_bits8 1://.
  case: (0 <= i < 2) => hi; last by rewrite W4u8.get_zero W8u8.get_out 1:/#.
  rewrite /= W4u8.pack4bE 1:// /= W8u8.pack8bE 1:/#.
  by have [|[|[|]]]-> : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 by smt().
qed.

lemma bits32_W8u8_red ws i :
  0 <= i < 2 =>
  W8u8.pack8_t ws \bits32 i =
    W4u8.pack4 [ws.[4 * i]; ws.[4 * i + 1]; ws.[4 * i + 2]; ws.[4 * i + 3] ].
proof. by move=> h;rewrite bits32_W8u8 h. qed.

lemma bits32_W16u8 ws i :
  W16u8.pack16_t ws \bits32 i =
    if 0 <= i < 4 then W4u8.pack4 [ws.[4 * i]; ws.[4 * i + 1]; ws.[4 * i + 2]; ws.[4 * i + 3] ] else W32.zero.
proof.
  apply W4u8.wordP => j hj.
  rewrite W128_bits32_bits8 1://.
  case: (0 <= i < 4) => hi; last by rewrite W4u8.get_zero W16u8.get_out 1:/#.
  rewrite /= W4u8.pack4bE 1:// /= W16u8.pack16bE 1:/#.
  by have [|[|[|]]]-> : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 by smt().
qed.

lemma bits32_W16u8_red ws i :
  0 <= i < 4 =>
  W16u8.pack16_t ws \bits32 i =
    W4u8.pack4 [ws.[4 * i]; ws.[4 * i + 1]; ws.[4 * i + 2]; ws.[4 * i + 3] ].
proof. by move=> h;rewrite bits32_W16u8 h. qed.

lemma bits32_W32u8 ws i :
  W32u8.pack32_t ws \bits32 i =
    if 0 <= i < 8 then W4u8.pack4 [ws.[4 * i]; ws.[4 * i + 1]; ws.[4 * i + 2]; ws.[4 * i + 3] ] else W32.zero.
proof.
  apply W4u8.wordP => j hj.
  rewrite W256_bits32_bits8 1://.
  case: (0 <= i < 8) => hi; last by rewrite W4u8.get_zero W32u8.get_out 1:/#.
  rewrite /= W4u8.pack4bE 1:// /= W32u8.pack32bE 1:/#.
  by have [|[|[|]]]-> : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 by smt().
qed.

lemma bits32_W32u8_red ws i :
  0 <= i < 8 =>
  W32u8.pack32_t ws \bits32 i =
    W4u8.pack4 [ws.[4 * i]; ws.[4 * i + 1]; ws.[4 * i + 2]; ws.[4 * i + 3] ].
proof. by move=> h;rewrite bits32_W32u8 h. qed.

hint simplify bits32_W8u8_red, bits32_W16u8_red, bits32_W32u8_red.

lemma bits32_W4u16 ws i :
  W4u16.pack4_t ws \bits32 i =
    if 0 <= i < 2 then W2u16.pack2 [ws.[2 * i]; ws.[2 * i + 1]] else W32.zero.
proof.
  apply W2u16.wordP => j hj.
  rewrite W64_bits32_bits16 1://.
  case: (0 <= i < 2) => hi; last by rewrite W2u16.get_zero W4u16.get_out 1:/#.
  rewrite /= W2u16.pack2bE 1:// /= W4u16.pack4bE 1:/#.
  by have []-> : j = 0 \/ j = 1 by smt().
qed.

lemma bits32_W4u16_red ws i :
  0 <= i < 2 =>
  W4u16.pack4_t ws \bits32 i = W2u16.pack2 [ws.[2 * i]; ws.[2 * i + 1]].
proof. by move=> h;rewrite bits32_W4u16 h. qed.

lemma bits32_W8u16 ws i :
  W8u16.pack8_t ws \bits32 i =
    if 0 <= i < 4 then W2u16.pack2 [ws.[2 * i]; ws.[2 * i + 1]] else W32.zero.
proof.
  apply W2u16.wordP => j hj.
  rewrite W128_bits32_bits16 1://.
  case: (0 <= i < 4) => hi; last by rewrite W2u16.get_zero W8u16.get_out 1:/#.
  rewrite /= W2u16.pack2bE 1:// /= W8u16.pack8bE 1:/#.
  by have []-> : j = 0 \/ j = 1 by smt().
qed.

lemma bits32_W8u16_red ws i :
  0 <= i < 4 =>
  W8u16.pack8_t ws \bits32 i = W2u16.pack2 [ws.[2 * i]; ws.[2 * i + 1]].
proof. by move=> h;rewrite bits32_W8u16 h. qed.

lemma bits32_W16u16 ws i :
  W16u16.pack16_t ws \bits32 i =
    if 0 <= i < 8 then W2u16.pack2 [ws.[2 * i]; ws.[2 * i + 1]] else W32.zero.
proof.
  apply W2u16.wordP => j hj.
  rewrite W256_bits32_bits16 1://.
  case: (0 <= i < 8) => hi; last by rewrite W2u16.get_zero W16u16.get_out 1:/#.
  rewrite /= W2u16.pack2bE 1:// /= W16u16.pack16bE 1:/#.
  by have []-> : j = 0 \/ j = 1 by smt().
qed.

lemma bits32_W16u16_red ws i :
  0 <= i < 8 =>
  W16u16.pack16_t ws \bits32 i = W2u16.pack2 [ws.[2 * i]; ws.[2 * i + 1]].
proof. by move=> h;rewrite bits32_W16u16 h. qed.

hint simplify bits32_W4u16_red, bits32_W8u16_red, bits32_W16u16_red.

lemma bits32_W2u64 ws i :
  W2u64.pack2_t ws \bits32 i = if 0 <= i < 4 then ws.[i%/2] \bits32 (i%%2) else W32.zero.
proof.
  apply W32.wordP => j hj; rewrite !bits32iE 1,2://.
  case: (0 <= i < 4) => /= hi; last by rewrite W128.get_out 1:/#.
  rewrite pack2wE 1:/#; have /= [-> ->] := divmod_mul 2 32 i j _ hj; 1: done; rewrite W2u32.bits32iE 1:// /#.
qed.

lemma bits32_W2u64_red ws i :
  0 <= i < 4 => W2u64.pack2_t ws \bits32 i = ws.[i%/2] \bits32 (i%%2).
proof. by move=> h;rewrite bits32_W2u64 h. qed.

lemma bits32_W4u64 ws i :
  W4u64.pack4_t ws \bits32 i = if 0 <= i < 8 then ws.[i%/2] \bits32 (i%%2) else W32.zero.
proof.
  apply W32.wordP => j hj; rewrite !bits32iE 1,2://.
  case: (0 <= i < 8) => /= hi; last by rewrite W256.get_out 1:/#.
  rewrite pack4wE 1:/#; have /= [-> ->] := divmod_mul 2 32 i j _ hj; 1: done; rewrite W2u32.bits32iE 1:// /#.
qed.

lemma bits32_W4u64_red ws i :
  0 <= i < 8 => W4u64.pack4_t ws \bits32 i = ws.[i%/2] \bits32 (i%%2).
proof. by move=> h;rewrite bits32_W4u64 h. qed.

hint simplify bits32_W2u64_red, bits32_W4u64_red.

lemma bits32_W2u128 ws i :
  W2u128.pack2_t ws \bits32 i = if 0 <= i < 8 then ws.[i%/4] \bits32 (i%%4) else W32.zero.
proof.
  apply W32.wordP => j hj; rewrite !bits32iE 1,2://.
  case: (0 <= i < 8) => /= hi; last by rewrite W256.get_out 1:/#.
  rewrite pack2wE 1:/#; have /= [-> ->] := divmod_mul 4 32 i j _ hj; 1: done; rewrite W4u32.bits32iE 1:// /#.
qed.

lemma bits32_W2u128_red ws i :
  0 <= i < 8 => W2u128.pack2_t ws \bits32 i = ws.[i%/4] \bits32 (i%%4).
proof. by move=> h;rewrite bits32_W2u128 h. qed.

hint simplify bits32_W2u128_red.

lemma W128_bits64_bits32 (w:W128.t) i j: 0 <= j < 2 => w \bits64 i \bits32 j = w \bits32 (2 * i + j).
proof.
  move=> hj; apply W32.wordP => k hk.
  by rewrite !bits32iE 1,2:// bits64iE 1:/#; congr; ring.
qed.

lemma W256_bits64_bits32 (w:W256.t) i j: 0 <= j < 2 => w \bits64 i \bits32 j = w \bits32 (2 * i + j).
proof.
  move=> hj; apply W32.wordP => k hk.
  by rewrite !bits32iE 1,2:// bits64iE 1:/#; congr; ring.
qed.

lemma W256_bits128_bits32 (w:W256.t) i j: 0 <= j < 4 => w \bits128 i \bits32 j = w \bits32 (4 * i + j).
proof.
  move=> hj; apply W32.wordP => k hk.
  by rewrite !bits32iE 1,2:// bits128iE 1:/#; congr; ring.
qed.

hint simplify W128_bits64_bits32, W256_bits64_bits32, W256_bits128_bits32.

(* --------------------------------------------------------------------------------- *)
(* Lemmas on \bits64                                                                 *)
(* --------------------------------------------------------------------------------- *)

lemma bits64_W16u8 ws i :
  W16u8.pack16_t ws \bits64 i =
    if 0 <= i < 2 then W8u8.pack8 [ws.[8 * i]; ws.[8 * i + 1]; ws.[8 * i + 2]; ws.[8 * i + 3];
                                   ws.[8 * i + 4]; ws.[8 * i + 5]; ws.[8 * i + 6]; ws.[8 * i + 7]]
    else W64.zero.
proof.
  apply W8u8.wordP => j hj.
  rewrite W128_bits64_bits8 1://.
  case: (0 <= i < 2) => hi; last by rewrite W8u8.get_zero W16u8.get_out 1:/#.
  rewrite /= W8u8.pack8bE 1:// /= W16u8.pack16bE 1:/#.
  by move: hj; rewrite -(mema_iota 0 8) -iotaredE /= => -[|[|[|[|[|[|[|]]]]]]] ->.
qed.

lemma bits64_W16u8_red ws i :
  0 <= i < 2 =>
  W16u8.pack16_t ws \bits64 i =
    W8u8.pack8 [ws.[8 * i]; ws.[8 * i + 1]; ws.[8 * i + 2]; ws.[8 * i + 3];
                ws.[8 * i + 4]; ws.[8 * i + 5]; ws.[8 * i + 6]; ws.[8 * i + 7]].
proof. by move=> h;rewrite bits64_W16u8 h. qed.

lemma bits64_W32u8 ws i :
  W32u8.pack32_t ws \bits64 i =
    if 0 <= i < 4 then W8u8.pack8 [ws.[8 * i]; ws.[8 * i + 1]; ws.[8 * i + 2]; ws.[8 * i + 3];
                                   ws.[8 * i + 4]; ws.[8 * i + 5]; ws.[8 * i + 6]; ws.[8 * i + 7]]
    else W64.zero.
proof.
  apply W8u8.wordP => j hj.
  rewrite W256_bits64_bits8 1://.
  case: (0 <= i < 4) => hi; last by rewrite W8u8.get_zero W32u8.get_out 1:/#.
  rewrite /= W8u8.pack8bE 1:// /= W32u8.pack32bE 1:/#.
  by move: hj; rewrite -(mema_iota 0 8) -iotaredE /= => -[|[|[|[|[|[|[|]]]]]]] ->.
qed.

lemma bits64_W32u8_red ws i :
  0 <= i < 4 =>
  W32u8.pack32_t ws \bits64 i =
    W8u8.pack8 [ws.[8 * i]; ws.[8 * i + 1]; ws.[8 * i + 2]; ws.[8 * i + 3];
                ws.[8 * i + 4]; ws.[8 * i + 5]; ws.[8 * i + 6]; ws.[8 * i + 7]].
proof. by move=> h;rewrite bits64_W32u8 h. qed.

hint simplify bits64_W16u8_red, bits64_W32u8_red.

lemma bits64_W8u16 ws i :
  W8u16.pack8_t ws \bits64 i =
    if 0 <= i < 2 then W4u16.pack4 [ws.[4 * i]; ws.[4 * i + 1]; ws.[4 * i + 2]; ws.[4 * i + 3] ] else W64.zero.
proof.
  apply W4u16.wordP => j hj.
  rewrite W128_bits64_bits16 1://.
  case: (0 <= i < 2) => hi; last by rewrite W4u16.get_zero W8u16.get_out 1:/#.
  rewrite /= W4u16.pack4bE 1:// /= W8u16.pack8bE 1:/#.
  by have [|[|[|]]]-> : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 by smt().
qed.

lemma bits64_W8u16_red ws i :
  0 <= i < 2 =>
  W8u16.pack8_t ws \bits64 i =
    W4u16.pack4 [ws.[4 * i]; ws.[4 * i + 1]; ws.[4 * i + 2]; ws.[4 * i + 3] ].
proof. by move=> h;rewrite bits64_W8u16 h. qed.

lemma bits64_W16u16 ws i :
  W16u16.pack16_t ws \bits64 i =
    if 0 <= i < 4 then W4u16.pack4 [ws.[4 * i]; ws.[4 * i + 1]; ws.[4 * i + 2]; ws.[4 * i + 3] ] else W64.zero.
proof.
  apply W4u16.wordP => j hj.
  rewrite W256_bits64_bits16 1://.
  case: (0 <= i < 4) => hi; last by rewrite W4u16.get_zero W16u16.get_out 1:/#.
  rewrite /= W4u16.pack4bE 1:// /= W16u16.pack16bE 1:/#.
  by have [|[|[|]]]-> : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 by smt().
qed.

lemma bits64_W16u16_red ws i :
  0 <= i < 4 =>
  W16u16.pack16_t ws \bits64 i =
    W4u16.pack4 [ws.[4 * i]; ws.[4 * i + 1]; ws.[4 * i + 2]; ws.[4 * i + 3] ].
proof. by move=> h;rewrite bits64_W16u16 h. qed.

hint simplify bits64_W8u16_red, bits64_W16u16_red.

lemma bits64_W4u32 ws i :
  W4u32.pack4_t ws \bits64 i =
    if 0 <= i < 2 then W2u32.pack2 [ws.[2 * i]; ws.[2 * i + 1]] else W64.zero.
proof.
  apply W2u32.wordP => j hj.
  rewrite W128_bits64_bits32 1://.
  case: (0 <= i < 2) => hi; last by rewrite W2u32.get_zero W4u32.get_out 1:/#.
  rewrite /= W2u32.pack2bE 1:// /= W4u32.pack4bE 1:/#.
  by have [|]-> : j = 0 \/ j = 1 by smt().
qed.

lemma bits64_W4u32_red ws i :
  0 <= i < 2 =>
  W4u32.pack4_t ws \bits64 i = W2u32.pack2 [ws.[2 * i]; ws.[2 * i + 1]].
proof. by move=> h;rewrite bits64_W4u32 h. qed.

lemma bits64_W8u32 ws i :
  W8u32.pack8_t ws \bits64 i =
    if 0 <= i < 4 then W2u32.pack2 [ws.[2 * i]; ws.[2 * i + 1]] else W64.zero.
proof.
  apply W2u32.wordP => j hj.
  rewrite W256_bits64_bits32 1://.
  case: (0 <= i < 4) => hi; last by rewrite W2u32.get_zero W8u32.get_out 1:/#.
  rewrite /= W2u32.pack2bE 1:// /= W8u32.pack8bE 1:/#.
  have [|]-> //= : j = 0 \/ j = 1 by smt().
qed.

lemma bits64_W8u32_red ws i :
  0 <= i < 4 =>
  W8u32.pack8_t ws \bits64 i = W2u32.pack2 [ws.[2 * i]; ws.[2 * i + 1]].
proof. by move=> h;rewrite bits64_W8u32 h. qed.

hint simplify bits64_W4u32_red, bits64_W8u32_red.

lemma bits64_W2u128 ws i :
  W2u128.pack2_t ws \bits64 i = if 0 <= i < 4 then ws.[i%/2] \bits64 (i%%2) else W64.zero.
proof.
  apply W64.wordP => j hj; rewrite !bits64iE 1,2://.
  case: (0 <= i < 4) => /= hi; last by rewrite W256.get_out 1:/#.
  rewrite pack2wE 1:/#; have /= [-> ->] := divmod_mul 2 64 i j _ hj; 1: done; rewrite W2u64.bits64iE 1:// /#.
qed.

lemma bits64_W2u128_red ws i :
  0 <= i < 4 => W2u128.pack2_t ws \bits64 i = ws.[i%/2] \bits64 (i%%2).
proof. by move=> h;rewrite bits64_W2u128 h. qed.

hint simplify bits64_W2u128_red.

lemma W256_bits128_bits64 (w:W256.t) i j: 0 <= j < 2 => w \bits128 i \bits64 j = w \bits64 (2 * i + j).
proof.
  move=> hj; apply W64.wordP => k hk.
  by rewrite !bits64iE 1,2:// bits128iE 1:/#; congr; ring.
qed.

hint simplify W256_bits128_bits64.

(* --------------------------------------------------------------------------------- *)
(* Lemmas on \bits128                                                                *)
(* --------------------------------------------------------------------------------- *)

lemma bits128_W32u8 ws i :
  W32u8.pack32_t ws \bits128 i =
   if  0 <= i < 2 then
    W16u8.pack16 [ws.[16 * i]; ws.[16 * i + 1]; ws.[16 * i + 2]; ws.[16 * i + 3];
                  ws.[16 * i + 4]; ws.[16 * i + 5]; ws.[16 * i + 6]; ws.[16 * i + 7];
                  ws.[16 * i + 8]; ws.[16 * i + 9]; ws.[16 * i + 10]; ws.[16 * i + 11];
                  ws.[16 * i + 12]; ws.[16 * i + 13]; ws.[16 * i + 14]; ws.[16 * i + 15]]
   else W128.zero.
proof.
  apply W16u8.wordP => j hj.
  rewrite W256_bits128_bits8 1://.
  case: (0 <= i < 2) => hi; last by rewrite W16u8.get_zero W32u8.get_out 1:/#.
  rewrite /= W32u8.pack32bE 1:/# /= W16u8.pack16bE 1:/#.
  by move: hj; rewrite -(mema_iota 0 16) -iotaredE/= => -[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|]]]]]]]]]]]]]]] ->.
qed.

lemma bits128_W32u8_red ws i :
  0 <= i < 2 =>
  W32u8.pack32_t ws \bits128 i =
    W16u8.pack16 [ws.[16 * i]; ws.[16 * i + 1]; ws.[16 * i + 2]; ws.[16 * i + 3];
                  ws.[16 * i + 4]; ws.[16 * i + 5]; ws.[16 * i + 6]; ws.[16 * i + 7];
                  ws.[16 * i + 8]; ws.[16 * i + 9]; ws.[16 * i + 10]; ws.[16 * i + 11];
                  ws.[16 * i + 12]; ws.[16 * i + 13]; ws.[16 * i + 14]; ws.[16 * i + 15]].
proof. by move=> hi;rewrite bits128_W32u8 hi. qed.

lemma bits128_W16u16 ws i :
  W16u16.pack16_t ws \bits128 i =
   if  0 <= i < 2 then
    W8u16.pack8 [ws.[8 * i]; ws.[8 * i + 1]; ws.[8 * i + 2]; ws.[8 * i + 3];
                 ws.[8 * i + 4]; ws.[8 * i + 5]; ws.[8 * i + 6]; ws.[8 * i + 7]]
   else W128.zero.
proof.
  apply W8u16.wordP => j hj.
  rewrite W256_bits128_bits16 1://.
  case: (0 <= i < 2) => hi; last by rewrite W8u16.get_zero W16u16.get_out 1:/#.
  rewrite /= W16u16.pack16bE 1:/# /= W8u16.pack8bE 1:/#.
  by move: hj; rewrite -(mema_iota 0 8) -iotaredE/= => -[|[|[|[|[|[|[|]]]]]]] ->.
qed.

lemma bits128_W16u16_red ws i :
  0 <= i < 2 =>
  W16u16.pack16_t ws \bits128 i =
    W8u16.pack8 [ws.[8 * i]; ws.[8 * i + 1]; ws.[8 * i + 2]; ws.[8 * i + 3];
                 ws.[8 * i + 4]; ws.[8 * i + 5]; ws.[8 * i + 6]; ws.[8 * i + 7]].
proof. by move=> hi;rewrite bits128_W16u16 hi. qed.

lemma bits128_W8u32 ws i :
  W8u32.pack8_t ws \bits128 i =
   if  0 <= i < 2 then
    W4u32.pack4 [ws.[4 * i]; ws.[4 * i + 1]; ws.[4 * i + 2]; ws.[4 * i + 3]]
   else W128.zero.
proof.
  apply W4u32.wordP => j hj.
  rewrite W256_bits128_bits32 1://.
  case: (0 <= i < 2) => hi; last by rewrite W4u32.get_zero W8u32.get_out 1:/#.
  rewrite /= W8u32.pack8bE 1:/# /= W4u32.pack4bE 1:/#.
  by move: hj; rewrite -(mema_iota 0 4) -iotaredE /= => -[|[|[|]]] ->.
qed.

lemma bits128_W8u32_red ws i :
  0 <= i < 2 =>
  W8u32.pack8_t ws \bits128 i =
    W4u32.pack4 [ws.[4 * i]; ws.[4 * i + 1]; ws.[4 * i + 2]; ws.[4 * i + 3]].
proof. by move=> hi;rewrite bits128_W8u32 hi. qed.

lemma bits128_W4u64 ws i :
  W4u64.pack4_t ws \bits128 i =
   if  0 <= i < 2 then
    W2u64.pack2 [ws.[2 * i]; ws.[2* i + 1]]
   else W128.zero.
proof.
  apply W2u64.wordP => j hj.
  rewrite W256_bits128_bits64 1://.
  case: (0 <= i < 2) => hi; last by rewrite W2u64.get_zero W4u64.get_out 1:/#.
  rewrite /= W4u64.pack4bE 1:/# /= W2u64.pack2bE 1:// get_of_list 1://.
  by move: hj; rewrite -(mema_iota 0 2) -iotaredE /= => -[|] ->.
qed.

lemma bits128_W4u64_red ws i :
  0 <= i < 2 =>
  W4u64.pack4_t ws \bits128 i = W2u64.pack2 [ws.[2 * i]; ws.[2* i + 1]].
proof. by move=> hi;rewrite bits128_W4u64 hi. qed.

hint simplify bits128_W32u8_red, bits128_W16u16_red, bits128_W8u32_red, bits128_W4u64_red.

(* --------------------------------------------------------------------------------- *)
(* Lemmas on pack                                                                    *)
(* --------------------------------------------------------------------------------- *)

lemma W2u16_W4u8 ws1 ws2 :
  pack2 [W2u8.pack2_t ws1; W2u8.pack2_t ws2] = pack4 [ws1.[0]; ws1.[1]; ws2.[0]; ws2.[1]].
proof. by apply W4u8.allP => /=. qed.

lemma W4u16_W8u8 ws1 ws2 ws3 ws4 :
  pack4 [W2u8.pack2_t ws1; W2u8.pack2_t ws2; W2u8.pack2_t ws3; W2u8.pack2_t ws4] =
  pack8 [ws1.[0]; ws1.[1]; ws2.[0]; ws2.[1]; ws3.[0]; ws3.[1]; ws4.[0]; ws4.[1]].
proof. by apply W8u8.allP => /=. qed.

lemma W8u16_W16u8 ws1 ws2 ws3 ws4 ws5 ws6 ws7 ws8:
  pack8 [W2u8.pack2_t ws1; W2u8.pack2_t ws2; W2u8.pack2_t ws3; W2u8.pack2_t ws4;
         W2u8.pack2_t ws5; W2u8.pack2_t ws6; W2u8.pack2_t ws7; W2u8.pack2_t ws8 ] =
  pack16 [ws1.[0]; ws1.[1]; ws2.[0]; ws2.[1]; ws3.[0]; ws3.[1]; ws4.[0]; ws4.[1];
         ws5.[0]; ws5.[1]; ws6.[0]; ws6.[1]; ws7.[0]; ws7.[1]; ws8.[0]; ws8.[1]].
proof. by apply W16u8.allP => /=. qed.

lemma W16u16_W32u8 ws1 ws2 ws3 ws4 ws5 ws6 ws7 ws8 ws9 ws10 ws11 ws12 ws13 ws14 ws15 ws16:
  pack16 [W2u8.pack2_t ws1; W2u8.pack2_t ws2; W2u8.pack2_t ws3; W2u8.pack2_t ws4;
          W2u8.pack2_t ws5; W2u8.pack2_t ws6; W2u8.pack2_t ws7; W2u8.pack2_t ws8;
          W2u8.pack2_t ws9; W2u8.pack2_t ws10; W2u8.pack2_t ws11; W2u8.pack2_t ws12;
          W2u8.pack2_t ws13; W2u8.pack2_t ws14; W2u8.pack2_t ws15; W2u8.pack2_t ws16] =
  pack32 [ws1.[0]; ws1.[1]; ws2.[0]; ws2.[1]; ws3.[0]; ws3.[1]; ws4.[0]; ws4.[1];
          ws5.[0]; ws5.[1]; ws6.[0]; ws6.[1]; ws7.[0]; ws7.[1]; ws8.[0]; ws8.[1];
          ws9.[0]; ws9.[1]; ws10.[0]; ws10.[1]; ws11.[0]; ws11.[1]; ws12.[0]; ws12.[1];
          ws13.[0]; ws13.[1]; ws14.[0]; ws14.[1]; ws15.[0]; ws15.[1]; ws16.[0]; ws16.[1]].
proof. by apply W32u8.allP => /=. qed.

(* hint simplify W2u16_W4u8, W4u16_W8u8, W8u16_W16u8, W16u16_W32u8. *)

lemma W2u32_W8u8 ws1 ws2 :
  pack2 [W4u8.pack4_t ws1; W4u8.pack4_t ws2] =
  pack8 [ws1.[0]; ws1.[1]; ws1.[2]; ws1.[3]; ws2.[0]; ws2.[1]; ws2.[2]; ws2.[3]].
proof. by apply W8u8.allP => /=. qed.

lemma W4u32_W16u8 ws1 ws2 ws3 ws4 :
  pack4 [W4u8.pack4_t ws1; W4u8.pack4_t ws2; W4u8.pack4_t ws3; W4u8.pack4_t ws4] =
  pack16 [ws1.[0]; ws1.[1]; ws1.[2]; ws1.[3]; ws2.[0]; ws2.[1]; ws2.[2]; ws2.[3];
          ws3.[0]; ws3.[1]; ws3.[2]; ws3.[3]; ws4.[0]; ws4.[1]; ws4.[2]; ws4.[3]].
proof. by apply W16u8.allP => /=. qed.

lemma W8u32_W32u8 ws1 ws2 ws3 ws4 ws5 ws6 ws7 ws8:
  pack8 [W4u8.pack4_t ws1; W4u8.pack4_t ws2; W4u8.pack4_t ws3; W4u8.pack4_t ws4;
         W4u8.pack4_t ws5; W4u8.pack4_t ws6; W4u8.pack4_t ws7; W4u8.pack4_t ws8 ] =
  pack32 [ws1.[0]; ws1.[1]; ws1.[2]; ws1.[3]; ws2.[0]; ws2.[1]; ws2.[2]; ws2.[3];
          ws3.[0]; ws3.[1]; ws3.[2]; ws3.[3]; ws4.[0]; ws4.[1]; ws4.[2]; ws4.[3];
          ws5.[0]; ws5.[1]; ws5.[2]; ws5.[3]; ws6.[0]; ws6.[1]; ws6.[2]; ws6.[3];
          ws7.[0]; ws7.[1]; ws7.[2]; ws7.[3]; ws8.[0]; ws8.[1]; ws8.[2]; ws8.[3]].
proof. by apply W32u8.allP => /=. qed.

hint simplify W2u32_W8u8, W4u32_W16u8, W8u32_W32u8.

lemma W2u64_W16u8 ws1 ws2:
  pack2 [W8u8.pack8_t ws1; W8u8.pack8_t ws2] =
  pack16 [ws1.[0]; ws1.[1]; ws1.[2]; ws1.[3]; ws1.[4]; ws1.[5]; ws1.[6]; ws1.[7];
          ws2.[0]; ws2.[1]; ws2.[2]; ws2.[3]; ws2.[4]; ws2.[5]; ws2.[6]; ws2.[7]].
proof. by apply W16u8.allP => /=. qed.

lemma W4u64_W32u8 ws1 ws2 ws3 ws4:
  pack4 [W8u8.pack8_t ws1; W8u8.pack8_t ws2; W8u8.pack8_t ws3; W8u8.pack8_t ws4] =
  pack32 [ws1.[0]; ws1.[1]; ws1.[2]; ws1.[3]; ws1.[4]; ws1.[5]; ws1.[6]; ws1.[7];
          ws2.[0]; ws2.[1]; ws2.[2]; ws2.[3]; ws2.[4]; ws2.[5]; ws2.[6]; ws2.[7];
          ws3.[0]; ws3.[1]; ws3.[2]; ws3.[3]; ws3.[4]; ws3.[5]; ws3.[6]; ws3.[7];
          ws4.[0]; ws4.[1]; ws4.[2]; ws4.[3]; ws4.[4]; ws4.[5]; ws4.[6]; ws4.[7]].
proof. by apply W32u8.allP => /=. qed.

hint simplify W2u64_W16u8, W4u64_W32u8.

lemma W2u128_W32u8 ws1 ws2:
  pack2 [W16u8.pack16_t ws1; W16u8.pack16_t ws2] =
  pack32 [ws1.[0]; ws1.[1]; ws1.[2]; ws1.[3]; ws1.[4]; ws1.[5]; ws1.[6]; ws1.[7];
          ws1.[8]; ws1.[9]; ws1.[10]; ws1.[11]; ws1.[12]; ws1.[13]; ws1.[14]; ws1.[15];
          ws2.[0]; ws2.[1]; ws2.[2]; ws2.[3]; ws2.[4]; ws2.[5]; ws2.[6]; ws2.[7];
          ws2.[8]; ws2.[9]; ws2.[10]; ws2.[11]; ws2.[12]; ws2.[13]; ws2.[14]; ws2.[15]].
proof. by apply W32u8.allP => /=. qed.

hint simplify W2u128_W32u8.

lemma W2u32_W4u16 ws1 ws2 :
  pack2 [W2u16.pack2_t ws1; W2u16.pack2_t ws2] = pack4 [ws1.[0]; ws1.[1]; ws2.[0]; ws2.[1]].
proof. by apply W4u16.allP => /=. qed.

lemma W4u32_W8u16 ws1 ws2 ws3 ws4 :
  pack4 [W2u16.pack2_t ws1; W2u16.pack2_t ws2; W2u16.pack2_t ws3; W2u16.pack2_t ws4] =
  pack8 [ws1.[0]; ws1.[1]; ws2.[0]; ws2.[1]; ws3.[0]; ws3.[1]; ws4.[0]; ws4.[1]].
proof. by apply W8u16.allP => /=. qed.

lemma W8u32_W16u16 ws1 ws2 ws3 ws4 ws5 ws6 ws7 ws8:
  pack8 [W2u16.pack2_t ws1; W2u16.pack2_t ws2; W2u16.pack2_t ws3; W2u16.pack2_t ws4;
         W2u16.pack2_t ws5; W2u16.pack2_t ws6; W2u16.pack2_t ws7; W2u16.pack2_t ws8 ] =
  pack16 [ws1.[0]; ws1.[1]; ws2.[0]; ws2.[1]; ws3.[0]; ws3.[1]; ws4.[0]; ws4.[1];
         ws5.[0]; ws5.[1]; ws6.[0]; ws6.[1]; ws7.[0]; ws7.[1]; ws8.[0]; ws8.[1]].
proof. by apply W16u16.allP => /=. qed.

lemma W2u128_W16u16 ws1 ws2 ws3 ws4 ws5 ws6 ws7 ws8
                    ws9 ws10 ws11 ws12 ws13 ws14 ws15 ws16 :
  pack2 [W8u16.pack8 [ws1; ws2; ws3; ws4; ws5; ws6; ws7; ws8];
         W8u16.pack8 [ws9; ws10; ws11; ws12; ws13; ws14; ws15; ws16] ] =
  pack16 [ws1; ws2; ws3; ws4; ws5; ws6; ws7; ws8;
         ws9; ws10; ws11; ws12; ws13; ws14; ws15; ws16].
proof. by apply W16u16.allP => /=. qed.

hint simplify W2u32_W4u16, W4u32_W8u16, W8u32_W16u16.

lemma W2u64_W8u16 ws1 ws2:
  pack2 [W4u16.pack4_t ws1; W4u16.pack4_t ws2] =
  pack8 [ws1.[0]; ws1.[1]; ws1.[2]; ws1.[3];
         ws2.[0]; ws2.[1]; ws2.[2]; ws2.[3]].
proof. by apply W8u16.allP => /=. qed.

lemma W4u64_W16u16 ws1 ws2 ws3 ws4:
  pack4 [W4u16.pack4_t ws1; W4u16.pack4_t ws2; W4u16.pack4_t ws3; W4u16.pack4_t ws4] =
  pack16 [ws1.[0]; ws1.[1]; ws1.[2]; ws1.[3]; ws2.[0]; ws2.[1]; ws2.[2]; ws2.[3];
          ws3.[0]; ws3.[1]; ws3.[2]; ws3.[3]; ws4.[0]; ws4.[1]; ws4.[2]; ws4.[3]].
proof. by apply W16u16.allP => /=. qed.

hint simplify W2u64_W8u16, W4u64_W16u16.

lemma W2u64_W4u32 ws1 ws2:
  pack2 [W2u32.pack2_t ws1; W2u32.pack2_t ws2] = pack4 [ws1.[0]; ws1.[1]; ws2.[0]; ws2.[1]].
proof. by apply W4u32.allP => /=. qed.

lemma W4u64_W8u32 ws1 ws2 ws3 ws4 :
  pack4 [W2u32.pack2_t ws1; W2u32.pack2_t ws2; W2u32.pack2_t ws3; W2u32.pack2_t ws4] =
  pack8 [ws1.[0]; ws1.[1]; ws2.[0]; ws2.[1]; ws3.[0]; ws3.[1]; ws4.[0]; ws4.[1]].
proof. by apply W8u32.allP => /=. qed.

lemma W2u128_W8u32 ws1 ws2 :
  pack2 [W4u32.pack4_t ws1; W4u32.pack4_t ws2] =
  pack8 [ws1.[0]; ws1.[1]; ws1.[2]; ws1.[3]; ws2.[0]; ws2.[1]; ws2.[2]; ws2.[3]].
proof. by apply W8u32.allP => /=. qed.

hint simplify W2u64_W4u32, W4u64_W8u32, W2u128_W8u32.

lemma W2u128_W4u64 ws1 ws2:
  pack2 [W2u64.pack2_t ws1; W2u64.pack2_t ws2] = pack4 [ws1.[0]; ws1.[1]; ws2.[0]; ws2.[1]].
proof. by apply W4u64.allP => /=. qed.

hint simplify W2u128_W4u64.
