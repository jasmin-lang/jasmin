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

(** This defines an example instance of the memory model.

The stack grows towards lower addresses, from the root to the bottom.

The stack is full when the “top” reaches the stack limit.

Stack frames are made of data (for local variables), meta-data (for code
introduced by the compiler) and padding (for enforcing alignment).

The pointer to the top is aligned during allocation
thanks to the introduction of enough padding.

The basic model maps each address to one bit (is this address allocated) and one
byte (the contents).

We additionally maintain two invariants:

 - the data part of each stack frame is allocated
 - the memory below the stack is free


*)

Require memory_model array type.

Import Utf8.
Import all_ssreflect all_algebra.
Import ZArith.
Import ssrZ.
Import type word utils gen_map.
Import memory_model.
Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Lemma zip_nil S T (m: seq T) : zip [::] m = @ nil (S * T).
Proof. by case: m. Qed.

Local Open Scope Z_scope.

Lemma aligned_factor s n :
  s != 0 →
  reflect (∃ q, n = q * s) (n mod s == 0).
Proof.
  move => /eqP s_pos; case: eqP => /Zmod_divides => - /(_ s_pos) h; constructor.
  - case: h => c; exists c; Psatz.lia.
  case => c ?; apply: h; exists c; Psatz.lia.
Qed.

Lemma orX (a b: bool) (P: Prop) :
  (a → P) →
  (a = false → b → P) →
  a || b → P.
Proof. by case: a => // _ /(_ erefl); case: b. Qed.

(* -------------------------------------------------------------------------- *)

Lemma subxx p :
  sub p p = 0.
Proof. by rewrite -{1}(add_0 p) sub_add. Qed.

Lemma add_p_opp_sub_add_p (p q: pointer) (n: Z) :
  add p (- sub (add p n) q + n) = q.
Proof.
  rewrite !addE !subE !(wrepr_add, wrepr_opp, wrepr_unsigned).
  ssrring.ssring.
Qed.

Corollary add_p_opp_sub_p (p q: pointer):
  add p (- sub p q) = q.
Proof.
  have := add_p_opp_sub_add_p p q 0.
  by rewrite add_0 Z.add_0_r.
Qed.

Lemma top_stack_after_alloc_bounded p ws sz :
  0 <= sz <= wunsigned p →
  wunsigned p - wunsigned (top_stack_after_alloc p ws sz) <= sz + wsize_size ws.
Proof.
  rewrite /top_stack_after_alloc /= => sz_pos.
  move: (align_word _ _) (align_word_range ws (p + wrepr Uptr (- sz))) => q.
  rewrite wunsigned_add; first Psatz.lia.
  have := wunsigned_range p.
  Psatz.lia.
Qed.

(** An example instance of the memory *)
Module MemoryI : MemoryT.

  Lemma addP p k: add p k = (p + wrepr U64 k)%R.
  Proof. done. Qed.

  Definition is_zalloc T (m: Mz.t T) (p:Z) : bool :=
    if Mz.get m p is Some _ then true else false.

  Record frame := { frame_size : Z ; frame_padding : Z }.

  Definition footprint_of_frame (f: frame) : Z :=
    frame_size f + frame_padding f.

  (** Total size of the stack, padding included *)
  Definition footprint_of_stack (frames: seq frame) :=
    foldr (λ f, Z.add (footprint_of_frame f)) 0 frames.

  (** Frames are valid when:
    - sizes are positive
    - stack does not overflow
  *)
  Definition valid_frame (f: frame) : bool :=
    (0 <=? frame_size f) && (0 <=? frame_padding f).

  Definition valid_frames (stk_limit stk_root: pointer) (frames: seq frame) :=
    all valid_frame frames && (footprint_of_stack frames <=? wunsigned stk_root - wunsigned stk_limit).

  (* The address [ptr] belongs to one stack frame *)
  Fixpoint pointer_into_stack (ptr: Z) (stk_root: pointer) (frames: seq frame) : bool :=
    if frames is f :: frames'
    then
      let: base := wunsigned stk_root - footprint_of_stack frames in
      (* pointer to this frame *)
      ((base <=? ptr) && (ptr <? base + frame_size f))
      ||
      (* pointer to an other frame *)
      pointer_into_stack ptr stk_root frames'
    else false (* no stack *).

  Record mem_ := {
    data      : Mz.t u8;
    alloc     : Mz.t unit;
    stk_root  : pointer; (* root of the stack *)
    stk_limit : pointer; (* limit of the stack *)
    frames    : seq frame; (* shape of the frames on the stack *)
    framesP   : valid_frames stk_limit stk_root frames;
    stk_allocP x : pointer_into_stack x stk_root frames → is_zalloc alloc x;
    stk_freeP x : 0 <= x < wunsigned stk_root - footprint_of_stack frames → is_zalloc alloc x = false;
  }.

  Arguments stk_allocP : clear implicits.
  Arguments stk_freeP : clear implicits.

  Definition mem := mem_.

  Definition is_alloc (m:mem) (p:pointer) :=
    is_zalloc m.(alloc) (wunsigned p).

  Definition is_init (m:mem) (p:pointer) :=
    is_zalloc m.(data) (wunsigned p).

(*  Lemma is_allocP m p ws :
    reflect (forall i, 0 <= i < wsize_size ws ->
               is_zalloc m.(alloc) (wunsigned (add p i)))
           (is_alloc m p ws).
  Proof.
    apply: equivP; first by apply allP.
    by split => h i hi; apply h; move: hi; rewrite in_ziota !zify Z.add_0_l.
  Qed.

  Lemma is_initE m p ws :
    is_init m p ws = all (fun i => is_init m (add p i) U8) (ziota 0 (wsize_size ws)).
  Proof.
    by rewrite /is_init /=; apply eq_in_all => ??; rewrite add_0 andbT.
  Qed.

  Lemma is_initP m p ws :
    reflect (forall i, 0 <= i < wsize_size ws -> is_init m (add p i) U8)
            (is_init m p ws).
  Proof.
    rewrite is_initE.
    apply: equivP; first by apply allP.
    split => h i hi.
    + by rewrite h // in_ziota !zify.
    by move: (h i) hi; rewrite in_ziota !zify Z.add_0_l /= add_0 => h1 /h1 [].
  Qed.
*)
(*
  Definition valid_pointer (m:mem) (p:pointer) (ws: wsize) :=
    is_align p ws && is_alloc m p ws.
*)

  Definition get (m:mem) (p:pointer) := 
    Let _ := assert (is_alloc m p && is_init m p) ErrAddrInvalid in
    ok (odflt 0%R (Mz.get m.(data) (wunsigned p))).

  Definition set (m:mem) (p:pointer) (w:u8) :=
    Let _ := assert (is_alloc m p) ErrAddrInvalid in
    ok {| data      := Mz.set m.(data) (wunsigned p) w ;
          alloc     := m.(alloc);
          stk_root  := m.(stk_root);
          stk_limit := m.(stk_limit);
          frames    := m.(frames);
          framesP   := m.(framesP);
          stk_allocP   := m.(stk_allocP);
          stk_freeP   := m.(stk_freeP);
       |}.

  Lemma is_allocP m p w : reflect (exists m', set m p w = ok m') (is_alloc m p).
  Proof.
    by (rewrite /set; case:is_alloc => /=; constructor) => [ | []//]; eexists;eauto.
  Qed.

  Lemma is_alloc_set m p w m' p' : set m p w = ok m' -> is_alloc m' p' = is_alloc m p'.
  Proof. by rewrite /set; t_xrbindP => _ _ <-. Qed.

  Lemma setP m p w p' m' :
    set m p w = ok m' ->
    get m' p' = if p == p' then ok w else get m p'.
  Proof.
    rewrite /set /get; t_xrbindP => _ /assertP ha <- /=.
    rewrite /is_init /is_alloc /=.
    case heq: is_zalloc => //=; last by move: ha heq; rewrite /is_alloc; case:eqP => // <- ->.
    rewrite /is_zalloc Mz.setP.
    have -> : (wunsigned p == wunsigned p') = (p == p'); last by case: eqP.
    apply: sameP; first by apply eqP.
    by apply (iffP eqP) => [-> | /wunsigned_inj].
  Qed.

  Lemma get_valid8 m p w : get m p = ok w -> is_alloc m p.
  Proof. by rewrite /get; t_xrbindP => _ /assertP /andP []. Qed.

  Instance CM : coreMem pointer mem :=
    CoreMem setP is_allocP get_valid8 is_alloc_set.

  Lemma is_align_wunsigned_add ptr ws i :
    is_align ptr ws →
    0 <= i < wsize_size ws →
    wunsigned (add ptr i) = wunsigned ptr + i.
  Proof.
    move => /is_align_no_overflow /lezP ??.
    rewrite wunsigned_add //.
    have := wunsigned_range ptr.
    Psatz.lia.
  Qed.

  Definition bounded (z1 z2 z3: Z) := (z1 <=? z2) && (z2 <? z3).

  Lemma footprint_of_valid_frame f :
    valid_frame f →
    0 <= footprint_of_frame f.
  Proof.
    case: f => s e /andP /=; rewrite !zify /footprint_of_frame => /= - [] s_pos e_pos.
    Psatz.lia.
  Qed.

  Lemma footprint_of_valid_frames frames :
    all valid_frame frames →
    0 <= footprint_of_stack frames.
  Proof.
    elim: frames; first reflexivity.
    move => f frames ih /= /andP[] /footprint_of_valid_frame ok_f /ih{ih}.
    Psatz.lia.
  Qed.

  Lemma frame_size_in_footprint f :
    valid_frame f →
    0 <= frame_size f <= footprint_of_frame f.
  Proof.
    case/andP; rewrite !zify => s_pos e_pos; split; first exact: s_pos.
    rewrite /footprint_of_frame.
    Psatz.lia.
  Qed.

  Lemma stack_range ptr stk_root frames :
    all valid_frame frames →
    pointer_into_stack ptr stk_root frames →
    wunsigned stk_root - footprint_of_stack frames <= ptr ∧ ptr < wunsigned stk_root.
  Proof.
    elim: frames => // f frames ih /andP[] ok_f ok_fr /orP[]; last first.
    - move => /ih{ih} /(_ ok_fr).
      have /= := footprint_of_valid_frame ok_f.
      Psatz.lia.
    rewrite !zify => {ih}.
    have := footprint_of_valid_frames ok_fr.
    have /= := frame_size_in_footprint ok_f.
    Psatz.lia.
  Qed.

  Definition top_stack (m:mem) :=
    add m.(stk_root) (- footprint_of_stack m.(frames)).

  Definition set_alloc_aux T b (m:Mz.t T) (ptr sz:Z) :=
    foldl (fun m k => if b is Some t then Mz.set m k t else Mz.remove m k) m (ziota ptr sz).

  Definition set_alloc b (m:Mz.t unit) (ptr sz:Z) :=
    set_alloc_aux (if b then Some tt else None) m ptr sz.

  Definition clear_data (m:Mz.t u8) (ptr sz:Z) :=
    set_alloc_aux None m ptr sz.

  Lemma set_alloc_auxP (T:eqType) (b:option T) m p sz x :
    Mz.get (set_alloc_aux b m p sz) x =
      if (p <=? x) && (x <? p + sz) then b else Mz.get m x.
  Proof.
    rewrite /set_alloc_aux -in_ziota; elim: ziota m => //= i l hrec m.
    rewrite in_cons hrec orbC; case: {hrec} b => [t | ];
    by case: ifP => //= ?;rewrite /is_zalloc (Mz.setP, Mz.removeP) eq_sym; case: ifP.
  Qed.

  Lemma set_allocP b m p sz x :
    is_zalloc (set_alloc b m p sz) x =
      if (p <=? x) && (x <? p + sz) then b else is_zalloc m x.
  Proof. by rewrite /is_zalloc set_alloc_auxP; case: ifP => //; case: b. Qed.

  Lemma clear_dataP m p sz x :
    is_zalloc (clear_data m p sz) x =
      is_zalloc m x && ~~((p <=? x) && (x <? p + sz)).
  Proof. by rewrite /is_zalloc set_alloc_auxP; case: ifP; rewrite /= (andbT, andbF). Qed.

  (** Stack blocks: association list of frame pointers to frame sizes (data only) *)
  Definition stack_blocks_rec stk_root (frames: seq frame) :=
    foldr (λ f '(p, blk), let: s := footprint_of_frame f in let: q := add p (- s) in (q, q :: blk)) (stk_root, [::]) frames.

  Definition stack_blocks stk_root frames : seq pointer :=
    (stack_blocks_rec stk_root frames).2.

  Definition stack_frames (m: mem) : seq pointer :=
    stack_blocks m.(stk_root) m.(frames).

  Lemma stack_blocks_rec_fst stk_root frames :
    (stack_blocks_rec stk_root frames).1 = add stk_root (- footprint_of_stack frames).
  Proof.
    elim: frames; first by rewrite add_0.
    move => f stk /=.
    case: (stack_blocks_rec _ _) => /= _ _ ->; rewrite addC; congr (add stk_root).
    Psatz.lia.
  Qed.

  Lemma stack_blocks_rec_snd stk_root frames :
    if (stack_blocks_rec stk_root frames).2 is p :: tl
    then p = add stk_root (- footprint_of_stack frames)
    else frames = [::].
  Proof.
    elim: frames => // f fr.
    have /= := (stack_blocks_rec_fst stk_root fr).
    case: (stack_blocks_rec _ _) => /= top [] //=.
    - move => -> -> /=; rewrite addC; congr (add _); Psatz.lia.
    case => _ _ _ -> _; rewrite addC; congr (add _); Psatz.lia.
  Qed.

  (** Allocation of a fresh block. *)
  Lemma alloc_stack_framesP (m: mem) s :
    valid_frame s && (footprint_of_frame s + footprint_of_stack m.(frames) <=? wunsigned m.(stk_root) - wunsigned m.(stk_limit)) →
    valid_frames m.(stk_limit) m.(stk_root) (s :: m.(frames)).
  Proof.
    case/andP => ok_s ofs; apply/andP; split; first (apply/andP; split).
    - exact: ok_s.
    - by have /andP[? _] := m.(framesP).
    exact: ofs.
  Qed.

  Lemma alloc_stack_stk_allocP (m: mem) f x :
    pointer_into_stack x (stk_root m) (f :: frames m) →
    is_zalloc (set_alloc true (alloc m) (wunsigned m.(stk_root) - (footprint_of_frame f + footprint_of_stack m.(frames))) f.(frame_size)) x.
  Proof.
    rewrite set_allocP /pointer_into_stack -/pointer_into_stack; apply: orX => -> //.
    exact: m.(stk_allocP).
  Qed.
  Arguments alloc_stack_stk_allocP [m f] x.

  Lemma alloc_stack_stk_freeP (m: mem) f x :
    (valid_frame f && (footprint_of_frame f + footprint_of_stack (frames m) <=? wunsigned (stk_root m) - wunsigned (stk_limit m))) →
    0 <= x < wunsigned (stk_root m) - footprint_of_stack (f :: frames m) →
    is_zalloc (set_alloc true (alloc m) (wunsigned (stk_root m) - (footprint_of_frame f + footprint_of_stack (frames m))) (frame_size f)) x = false.
  Proof.
    case/andP => /footprint_of_valid_frame ok_f ok_ws /= range.
    rewrite set_allocP.
    case: ifPn; rewrite !zify; first Psatz.lia.
    move => nrange.
    apply: m.(stk_freeP).
    Psatz.lia.
  Qed.

  Definition alloc_stack (m: mem) (ws: wsize) (sz sz': Z) : exec mem :=
    let: top := align_word ws (add (top_stack m) (- (sz + sz'))) in
    let: padding := sub (top_stack m) top - sz in
    let: f := {| frame_size := sz ; frame_padding := padding |} in
    let: ok_f := valid_frame f in
    let: no_overflow := footprint_of_frame f + footprint_of_stack (frames m) <=? wunsigned (stk_root m) - wunsigned (stk_limit m) in
    match Sumbool.sumbool_of_bool (ok_f && no_overflow) with
    | right _ => Error ErrStack
    | left C =>
      ok
        {| data := clear_data m.(data) (wunsigned m.(stk_root) - (footprint_of_frame f + footprint_of_stack m.(frames))) f.(frame_size);
           alloc := set_alloc true m.(alloc) (wunsigned m.(stk_root) - (footprint_of_frame f + footprint_of_stack m.(frames))) f.(frame_size);
           stk_root := m.(stk_root);
           stk_limit := m.(stk_limit);
           frames := f :: m.(frames);
           framesP := alloc_stack_framesP C;
           stk_allocP x := alloc_stack_stk_allocP x;
           stk_freeP x :=  alloc_stack_stk_freeP C;
        |}
    end.

  (** Free *)
  Lemma free_stack_framesP (m: mem) :
    valid_frames (stk_limit m) (stk_root m) (behead (frames m)).
  Proof.
    have /andP[h /lezP k] := m.(framesP).
    apply/andP; split.
    - by case: {k} (frames m) h => //= ? ? /andP[].
    rewrite zify.
    have [??] := wunsigned_range m.(stk_root).
    case: (frames m) h k => // f fs /andP[] /footprint_of_valid_frame ? _ /=.
    Psatz.lia.
  Qed.

  Lemma free_stack_stk_allocP (m: mem) x :
    pointer_into_stack x (stk_root m) (behead (frames m)) →
    is_zalloc (set_alloc false (alloc m) (wunsigned (stk_root m) - footprint_of_stack (frames m)) (odflt 0 (omap footprint_of_frame (ohead (frames m))))) x.
  Proof.
    case: (frames m) m.(framesP) m.(stk_allocP) => // f frames /andP[] /= /andP[] ok_f valid_frames /lezP no_overflow /(_ x) old_allocated range.
    rewrite set_allocP.
    move: old_allocated; rewrite range orbT => /(_ erefl) ->.
    have := stack_range valid_frames range.
    case: andP => //; rewrite !zify {range}.
    Psatz.lia.
  Qed.
  Arguments free_stack_stk_allocP : clear implicits.

  Lemma free_stack_stk_freeP (m: mem) x :
    0 <= x < wunsigned (stk_root m) - footprint_of_stack (behead (frames m)) →
    is_zalloc (set_alloc false (alloc m) (wunsigned (stk_root m) - footprint_of_stack (frames m)) (odflt 0 (omap footprint_of_frame (ohead (frames m))))) x = false.
  Proof.
    move => range.
    have old_free := m.(stk_freeP) x.
    rewrite set_allocP; case: ifPn => // nrange.
    apply: old_free.
    split; first Psatz.lia.
    case: (frames m) m.(framesP) range nrange => //= f stk; first Psatz.lia.
    case/andP => /= /andP[] _ valid_frames _.
    have := footprint_of_valid_frames valid_frames.
    rewrite !zify; Psatz.lia.
  Qed.
  Arguments free_stack_stk_freeP : clear implicits.

  Definition free_stack (m: mem) : mem :=
    let sz := odflt 0 (omap footprint_of_frame (ohead m.(frames))) in
    {| data := m.(data);
       alloc := set_alloc false m.(alloc) (wunsigned m.(stk_root) - (footprint_of_stack m.(frames))) sz;
       stk_root := m.(stk_root);
       stk_limit := m.(stk_limit);
       frames := behead m.(frames);
       framesP := free_stack_framesP m;
       stk_allocP := free_stack_stk_allocP m;
       stk_freeP := free_stack_stk_freeP m;
    |}.

  (** Initial memory: empty with pre-allocated blocks.
    The stack is rooted at the higest aligned pointer below the lowest allocated address.
   *)
  Definition init_mem_alloc (s: seq (pointer * Z)) : Mz.t unit :=
    foldl (fun a pz => set_alloc true a (wunsigned pz.1) pz.2) (Mz.empty _) s.

  Definition all_above (s: seq (pointer * Z)) (stk: pointer) : bool :=
    all (λ '(p, _), wlt Unsigned stk p) s.

  Lemma init_mem_framesP stk_root :
    valid_frames 0 stk_root [::].
  Proof. apply/lezP; rewrite Z.sub_0_r; exact: (proj1 (wunsigned_range _)). Qed.

  Lemma init_mem_stk_allocP (stk_root: pointer) s x :
    false →
    is_zalloc (init_mem_alloc s) x.
  Proof. by []. Qed.

  Lemma init_mem_stk_freeP_aux s stk m :
    all_above s stk →
    ∀ x,
      0 <= x <= wunsigned stk →
      is_zalloc (foldl (λ a pz, set_alloc true a (wunsigned pz.1) pz.2) m s) x = is_zalloc m x.
  Proof.
    rewrite /all_above.
    elim: s m => //= - [p z] s ih m /andP[] /ltzP ok_p {}/ih ih x x_range.
    rewrite (ih _ _ x_range) {ih} set_allocP /=.
    move: ok_p; rewrite -/(wunsigned stk) -/(wunsigned p) => ok_p.
    case: andP => //; rewrite !zify.
    Psatz.lia.
  Qed.

  Lemma init_mem_stk_freeP s stk x :
   all_above s stk →
    0 <= x < wunsigned stk - 0 →
    is_zalloc (init_mem_alloc s) x = false.
  Proof.
    move => all_above x_range.
    rewrite /init_mem_alloc (init_mem_stk_freeP_aux (Mz.empty _) all_above) //; Psatz.lia.
  Qed.
  Arguments init_mem_stk_freeP : clear implicits.

  Definition init_mem (s: seq (pointer * Z)) (stk: pointer) : exec mem :=
    match Sumbool.sumbool_of_bool (is_align stk U256) with
    | right _ => Error ErrStack
    | left stk_align =>
    match Sumbool.sumbool_of_bool (all_above s stk) with
    | right _ => Error ErrStack
    | left stk_below =>
      ok
        {| data := Mz.empty _;
           alloc := init_mem_alloc s;
           stk_limit := 0%R;
           stk_root := stk;
           frames := [::];
           framesP := init_mem_framesP stk;
           stk_allocP := init_mem_stk_allocP stk s;
           stk_freeP p := init_mem_stk_freeP s stk p stk_below;
        |}
    end end.

  Lemma _top_stackE (m: mem) :
    head (stk_root m) (stack_frames m) = top_stack m.
  Proof.
    rewrite /stack_frames /top_stack /stack_blocks.
    have := stack_blocks_rec_snd (stk_root m) (frames m).
    case: (stack_blocks_rec _ _) => /= _ [] //.
    by move => ->; rewrite add_0.
  Qed.

  Lemma stack_region_is_free (m: mem) (p: pointer) :
    wunsigned (stk_limit m) <= wunsigned p < wunsigned (head (stk_root m) (stack_frames m)) →
    ~~ validw m p U8.
  Proof.
    rewrite _top_stackE => - [] p_lo p_hi.
    rewrite /validw is_align8 /= add_0 andbT /is_alloc (stk_freeP m) //; split.
    + by have [] := wunsigned_range p.
    move: p_hi; rewrite /top_stack.
    rewrite wunsigned_add //.
    have /andP[/footprint_of_valid_frames] := framesP m.
    rewrite zify.
    have := wunsigned_range (stk_root m).
    have := wunsigned_range (stk_limit m).
    Psatz.lia.
  Qed.

  Instance M : memory CM  :=
    Memory stk_root stk_limit stack_frames alloc_stack free_stack init_mem stack_region_is_free.

  Lemma top_stackE (m: mem) :
    memory_model.top_stack m = top_stack m.
  Proof. exact: _top_stackE. Qed.

  Lemma write_mem_invariant T (P: mem → T) :
    (∀ m p v,
      is_alloc m p →
      P {| data := Mz.set (data m) (wunsigned p) v;
           alloc := alloc m;
           stk_root := stk_root m;
           stk_limit := stk_limit m;
           frames := frames m;
           framesP := framesP m;
           stk_allocP := stk_allocP m;
           stk_freeP := stk_freeP m |} = P m) →
    ∀ m p s (v: word s) m',
      write m p v = ok m' →
      P m  = P m'.
  Proof.
    move => K m p s v m'; rewrite /write; t_xrbindP => _ _.
    elim: ziota m => //=; first by move=> ? [->].
    by move=> ?? hrec; rewrite {2}/set; t_xrbindP => ??? /assertP /K h <- /hrec <-.
  Qed.

  Lemma top_stack_write_mem m p s (v: word s) m' :
    write m p v = ok m' →
    top_stack m = top_stack m'.
  Proof. by apply write_mem_invariant. Qed.

  Lemma write_mem_stable m m' p s (v:word s) :
    write m p v = ok m' -> stack_stable m m'.
  Proof. by move => ok_m'; split => /=; exact: write_mem_invariant ok_m'. Qed.

  (** Allocation *)
  Lemma footprint_of_stack_pos (m: mem) :
    0 <= footprint_of_stack m.(frames).
  Proof.
    have /andP[h _] := m.(framesP).
    exact: footprint_of_valid_frames.
  Qed.
  Arguments footprint_of_stack_pos : clear implicits.

  Lemma Zleb_succ (x y: Z) :
    (x + 1 <=? y) = (x <? y).
  Proof. case: Z.leb_spec; case: Z.ltb_spec => //; Psatz.lia. Qed.

  Lemma ass_valid m ws_stk sz sz' m' :
    alloc_stack m ws_stk sz sz' = ok m' →
    ∀ p,
    validw m' p U8 =
    validw m p U8 || between (top_stack m') sz p U8.
  Proof.
    rewrite /alloc_stack; case: Sumbool.sumbool_of_bool => // h [<-] p.
    rewrite -!valid8_validw /valid8 /= /is_alloc /top_stack /=.
    case/andP: h.
    set fr := {| frame_size := sz |} => ok_f /lezP no_ovf.
    rewrite set_allocP /between.
    have b_pos := wunsigned_range m.(stk_root).
    have l_pos := wunsigned_range m.(stk_limit).
    have f_pos := footprint_of_stack_pos m.
    have s_pos := footprint_of_valid_frame ok_f.
    rewrite wunsigned_add; last Psatz.lia.
    rewrite Zleb_succ.
    by case: ifP => _; rewrite (orbT, orbF).
  Qed.

  Lemma ass_fresh m ws_stk sz sz' m' :
    alloc_stack m ws_stk sz sz' = ok m' →
    ∀ p s,
      validw m p s →
      (wunsigned p + wsize_size s <= wunsigned (top_stack m') ∨ wunsigned (top_stack m') + sz <= wunsigned p).
  Proof.
    move => X; have := m.(stk_freeP); move: X.
    rewrite /alloc_stack; case: Sumbool.sumbool_of_bool => // h [<-] /= stk_fresh p s /andP[] p_align p_alloc.
    rewrite /top_stack /=.
    right. apply/lezP; case: lezP => // /Z.nle_gt X.
    rewrite -(stk_fresh (wunsigned p)).
    - by move/allP: p_alloc => /(_ 0); rewrite in_ziota /= (proj2 (Z.ltb_lt _ _) (wsize_size_pos s)) add_0 => /(_ erefl).
    split. apply wunsigned_range.
    apply: (Z.lt_le_trans _ _ _ X).
    clear X.
    case/andP: h => ok_f /lezP ovf.
    have rt_range := wunsigned_range (stk_root m).
    have l_range := wunsigned_range (stk_limit m).
    have {ok_f}/= := frame_size_in_footprint ok_f.
    move: (footprint_of_frame _) ovf => fr ovf fr_pos.
    have /andP[/footprint_of_valid_frames ok_s _] := framesP m.
    rewrite wunsigned_add; Psatz.lia.
  Qed.

  Lemma ass_init m ws_stk sz sz' m' :
    alloc_stack m ws_stk sz sz' = ok m' →
    ∀ p,
     is_init m' p = is_init m p && ~~between (top_stack m') sz p U8.
  Proof.
    rewrite /alloc_stack; case: Sumbool.sumbool_of_bool => // h [<-] p.
    rewrite /= /is_init /top_stack /=.
    case/andP: h.
    set fr := {| frame_size := sz |} => ok_f /lezP no_ovf.
    rewrite clear_dataP /between.
    have b_pos := wunsigned_range m.(stk_root).
    have l_pos := wunsigned_range m.(stk_limit).
    have f_pos := footprint_of_stack_pos m.
    have s_pos := footprint_of_valid_frame ok_f.
    rewrite wunsigned_add; last Psatz.lia.
    by rewrite Zleb_succ.
  Qed.

  Lemma ass_read_old8 m ws_stk sz sz' m' :
    alloc_stack m ws_stk sz sz' = ok m' →
    ∀ p,
    validw m p U8 →
    read m p U8 = read m' p U8.
  Proof.
    move => ok_m' p ok_m_p.
    have : validw m' p U8 by rewrite (ass_valid ok_m') ok_m_p.
    have := ass_fresh ok_m' ok_m_p.
    move: ok_m_p; rewrite -!valid8_validw -!get_read8 /memory_model.get /= /get wsize8.
    move=> -> hfresh ->; rewrite (ass_init ok_m').
    have -> : ~~ between (top_stack m') sz p U8.
    + by rewrite /between !zify wsize8; Psatz.lia.
    rewrite /= andbT.
    move: ok_m' hfresh.
    rewrite /alloc_stack; case: Sumbool.sumbool_of_bool => // h [<-].
    rewrite /top_stack /= => /= hfresh.
    case heq: is_init => //=; do 2!f_equal.
    rewrite /= /clear_data set_alloc_auxP.
    case: ifP => //.
    case/andP: h hfresh.
    set fr := {| frame_size := sz |} => ok_f /lezP no_ovf.
    have b_pos := wunsigned_range m.(stk_root).
    have l_pos := wunsigned_range m.(stk_limit).
    have f_pos := footprint_of_stack_pos m.
    have s_pos := footprint_of_valid_frame ok_f.
    rewrite !zify wunsigned_add; Psatz.lia.
  Qed.

  Lemma ass_read_new m ws_stk sz sz' m' :
    alloc_stack m ws_stk sz sz' = ok m' →
    ∀ p,
    ~validw m p U8 → validw m' p U8 →
    read m' p U8 = Error ErrAddrInvalid.
  Proof.
    move=> ha p.
    rewrite (ass_valid ha) => /negP /negbTE -> /=.
    rewrite -get_read8 /memory_model.get /= /get (ass_init ha) => ->.
    by rewrite !andbF.
  Qed.

  Lemma ass_align m ws_stk sz sz' m' :
    alloc_stack m ws_stk sz sz' = ok m' →
    is_align (top_stack m') ws_stk.
  Proof.
    rewrite /alloc_stack; case: Sumbool.sumbool_of_bool => // h [<-].
    rewrite /top_stack /=.
    move: h => /andP[] /andP[] /= /ZleP ok_f /lezP sz_pos.
    have /andP[ok_fs _] := framesP m.
    have fs_pos := footprint_of_valid_frames ok_fs.
    rewrite /footprint_of_frame /=.
    move: (footprint_of_stack _) sz_pos fs_pos => fs sz_pos fs_pos _.
    rewrite !addE !subE !(wrepr_opp, wrepr_add, wrepr_unsigned, align_wordE).
    set x := (X in is_align X).
    have -> : x = align_word ws_stk (stk_root m - wrepr U64 fs - (wrepr U64 sz + wrepr U64 sz')).
    + by rewrite /x;ssrring.ssring.
    rewrite /is_align p_to_zE; apply align_word_aligned.
  Qed.

  Lemma ass_above_limit m ws_stk sz sz' m' :
    alloc_stack m ws_stk sz sz' = ok m' →
    wunsigned (stack_limit m) <= wunsigned (top_stack m')
    ∧ wunsigned (top_stack m') + sz <= wunsigned (top_stack m).
  Proof.
    rewrite /alloc_stack; case: Sumbool.sumbool_of_bool => // h [<-].
    rewrite /top_stack /=.
    rewrite !addE.
    case/andP: h => ok_f /lezP.
    case/andP: (ok_f) => /lezP /= sz_pos /lezP padding_pos.
    have {ok_f} := footprint_of_valid_frame ok_f.
    set f := {| frame_size := sz |}.
    move => f_pos h.
    have fs_pos := footprint_of_stack_pos m.
    have limit_range := wunsigned_range (stk_limit m).
    have root_range := wunsigned_range (stk_root m).
    rewrite !wunsigned_add; first split.
    1, 3-4: Psatz.lia.
    rewrite /f /footprint_of_frame /=.
    Psatz.lia.
  Qed.

  Lemma ass_root m ws_stk sz sz' m' :
    alloc_stack m ws_stk sz sz' = ok m' →
    stack_root m' = stack_root m.
  Proof. by rewrite /alloc_stack; case: Sumbool.sumbool_of_bool => // h [<-]. Qed.

  Lemma ass_limit m ws_stk sz sz' m' :
    alloc_stack m ws_stk sz sz' = ok m' →
    stack_limit m' = stack_limit m.
  Proof. by rewrite /alloc_stack; case: Sumbool.sumbool_of_bool => // h [<-]. Qed.

  Lemma ass_frames m ws_stk sz sz' m' :
    alloc_stack m ws_stk sz sz' = ok m' →
    stack_frames m' = top_stack_after_alloc (top_stack m) ws_stk (sz + sz') :: stack_frames m.
  Proof.
    rewrite /alloc_stack; case: Sumbool.sumbool_of_bool => // h [<-] /=.
    rewrite /stack_frames /=.
    rewrite {1}/stack_blocks /=.
    case heq: (stack_blocks_rec _ _) => [p blk].
    rewrite /stack_blocks heq /=.
    rewrite {1}/top_stack -stack_blocks_rec_fst heq /=.
    congr cons.
    rewrite /top_stack_after_alloc.
    move: (align_word _ _) => q.
    rewrite /footprint_of_frame /=.
    by rewrite Zplus_minus add_p_opp_sub_p.
  Qed.

  Lemma alloc_stackP m m' ws_stk sz sz' :
    alloc_stack m ws_stk sz sz' = ok m' -> alloc_stack_spec m ws_stk sz sz' m'.
  Proof.
    move => o.
    split; rewrite ?top_stackE.
    - exact: ass_read_old8 o.
    - exact: ass_read_new o.
    - exact: ass_valid o.
    - exact: ass_align o.
    - exact: ass_above_limit o.
    - exact: ass_fresh o.
    - exact: ass_root o.
    - exact: ass_limit o.
    exact: ass_frames o.
  Qed.

  Lemma first_frameE (m: mem) :
    odflt 0 (omap footprint_of_frame (ohead (frames m))) = wunsigned (top_stack (free_stack m)) - wunsigned (top_stack m).
  Proof.
    rewrite /top_stack /=.
    have /andP[] := framesP m.
    case: (frames m) => /=.
    + rewrite add_0; Psatz.lia.
    move => f fr /andP[] ok_f ok_fr /lezP noovf.
    have ff := footprint_of_valid_frame ok_f.
    have fs := footprint_of_valid_frames ok_fr.
    have rr := wunsigned_range (stk_root m).
    have lr := wunsigned_range (stk_limit m).
    rewrite !wunsigned_add; Psatz.lia.
  Qed.

  Lemma wunsigned_top_stack m :
    wunsigned (top_stack m) = wunsigned (stk_root m) - footprint_of_stack (frames m).
  Proof.
    have /andP[ /footprint_of_valid_frames ? /lezP h ] := framesP m.
    rewrite /top_stack wunsigned_add //.
    have := wunsigned_range (stk_root m).
    have := wunsigned_range (stk_limit m).
    Psatz.lia.
  Qed.

  Lemma fss_valid m p :
    validw (free_stack m) p U8 = validw m p U8 && ~~ pointer_range (top_stack m) (top_stack (free_stack m)) p.
  Proof.
    rewrite -!valid8_validw /valid8 /=.
    rewrite /is_alloc /= set_allocP.
    set B := (X in if X then _ else _).
    suff -> : B = pointer_range (top_stack m) (top_stack (free_stack m)) p.
    + by case: ifP => _; rewrite ?andbF ?andbT.
    subst B.
    have P (a b: bool) : a ↔ b → a = b :> bool.
    + case: a b => - [] //; last by intuition.
      by case => /(_ erefl).
    apply: P.
    rewrite !zify first_frameE !wunsigned_top_stack.
    change (stk_root (free_stack m)) with (stk_root m).
    Psatz.lia.
  Qed.

  Lemma fss_read_old8 m p :
    validw (free_stack m) p U8 →
    read m p U8 = read (free_stack m) p U8.
  Proof.
    move => /dup [] hv'; rewrite (fss_valid m) => /andP[] hv hp.
    by move: hv' hv; rewrite -!valid8_validw -!get_read8 /memory_model.get /= /get => -> ->.  
  Qed.

  Lemma free_stackP m :
    free_stack_spec m (free_stack m).
  Proof.
    split => *.
    - exact: fss_read_old8.
    - rewrite !top_stackE; exact: fss_valid.
    - by [].
    - by [].
    rewrite /memory_model.frames /= /stack_frames /= /stack_blocks.
    case: (frames m) => //= f fr.
    by case: (stack_blocks_rec _ _).
  Qed.

  Lemma top_stack_after_aligned_alloc p ws sz :
    is_align p ws →
    top_stack_after_alloc p ws sz = (p + wrepr Uptr (- round_ws ws sz))%R.
  Proof.
    rewrite /top_stack_after_alloc /is_align p_to_zE /= => /eqP => hmod.
    rewrite -(wrepr_unsigned (align_word _ _)) !wrepr_opp align_wordE.
    have hlt : wsize_size ws > 0.
    + by have := wsize_size_pos ws.
    have hmm : forall k, k mod wbase U64 mod wsize_size ws = k mod wsize_size ws.
    + move=> k; rewrite -Znumtheory.Zmod_div_mod //.
      by apply Znumtheory.Zmod_divide => //; case: (ws).
    rewrite wrepr_sub wrepr_unsigned.
    rewrite -{2}(wrepr_unsigned p) -{2}(wrepr_unsigned (wrepr _ _)) -wrepr_sub wunsigned_repr hmm.
    set sz' := wunsigned (wrepr U64 sz).
    have -> : (wunsigned p - sz') mod wsize_size ws = (-sz') mod wsize_size ws.
    + by rewrite (Z_div_mod_eq (wunsigned p) _ hlt) hmod Z.add_0_r /Z.sub
       Z.add_comm Z.mul_comm Z_mod_plus_full.
    have -> : (-sz') mod wsize_size ws =
       if sz' mod wsize_size ws == 0 then 0 else wsize_size ws - sz' mod wsize_size ws.
    + case: eqP; first by apply Z_mod_zero_opp_full.
      by apply Z_mod_nz_opp_full.
    rewrite /sz' wunsigned_repr hmm.
    have := Z_div_mod sz (wsize_size ws) hlt.
    rewrite /round_ws /Z.modulo.
    case: Z.div_eucl => q r [-> ] ?; case: eqP => [ -> | ?].
    + by rewrite wrepr0 GRing.subr0.
    rewrite -GRing.addrA -GRing.opprB GRing.opprK -wrepr_add; do 3!f_equal; ring.
  Qed.

  Lemma alloc_stack_complete m ws sz sz' :
    let: old_size:= wunsigned (stack_root m) - wunsigned (memory_model.top_stack m) in
    let: max_size := wunsigned (stack_root m) - wunsigned (stack_limit m) in
    let: available := max_size - old_size in
    [&& 0 <=? sz, 0 <=? sz' &
    if is_align (memory_model.top_stack m) ws
    then round_ws ws (sz + sz') <=? available (* tight bound *)
    else sz + sz' + wsize_size ws <=? available (* loose bound, exact behavior is under-specified *)
    ] →
    ∃ m', alloc_stack m ws sz sz' = ok m'.
  Proof.
    rewrite !top_stackE !zify => - [ sz_pos ] [ sz'_pos ].
    rewrite /alloc_stack.
    rewrite /valid_frame /=.
    case: Sumbool.sumbool_of_bool; first by eauto.
    rewrite /footprint_of_frame /=.
    move => /negbT; rewrite !zify => X no_overflow; elim: X.
    refine ((λ x, conj (conj sz_pos (proj1 x)) (proj2 x)) _).
    have -> : footprint_of_stack (frames m) = wunsigned (stk_root m) - wunsigned (top_stack m).
    - by rewrite wunsigned_top_stack; ring.
    rewrite !subE.
    rewrite -/(top_stack_after_alloc (top_stack m) ws (sz + sz')).
    case: ifPn no_overflow => top_align; rewrite zify => no_overflow.
    { (* old top stack is aligned for ws *)
      have size_big := @round_ws_range ws (sz + sz').
      have size_small : 0 <= round_ws ws (sz + sz') <= wunsigned (top_stack m).
      - have := wunsigned_range (stk_limit m).
        Psatz.lia.
      rewrite top_stack_after_aligned_alloc //.
      rewrite GRing.opprD GRing.addrA GRing.subrr wrepr_opp GRing.opprK GRing.add0r.
      by have ? := wunsigned_range (top_stack m); rewrite wunsigned_repr_small; Psatz.lia.
    }
    (* old top stack is not aligned *)
    rewrite /top_stack_after_alloc.
    rewrite -(wrepr_unsigned (align_word _ _)).
    rewrite align_wordE wrepr_sub wrepr_unsigned.
    rewrite 2!GRing.opprD !GRing.addrA GRing.subrr GRing.add0r wrepr_opp !GRing.opprK.
    set x := (_ mod _).
    have ? := wsize_size_pos ws.
    have ? : 0 <= x < wsize_size ws by apply Z.mod_pos_bound.
    rewrite -wrepr_add.
    have ? := wunsigned_range (stk_limit m).
    have ? := wunsigned_range (top_stack m).
    rewrite wunsigned_repr_small; Psatz.lia.
  Qed.

End MemoryI.
