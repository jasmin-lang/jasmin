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

  Stack allocation is not described.
*)

Require memory_model array.

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

Lemma cut_wbase_Uptr sz :
  wbase Uptr = (wsize_size sz * CoqWord.word.modulus (nat63.+3 - (Nat.log2 (wsize_size_minus_1 sz))))%Z.
Proof. by case: sz; vm_compute. Qed.

Local Open Scope Z_scope.

(* -------------------------------------------------------------------------- *)

Module Align.

Local Notation is_align ptr ws :=
  (let w := wunsigned ptr in
  (w mod wsize_size ws == 0)%Z).

Lemma is_align_array ptr sz j :
  is_align ptr sz → is_align (wrepr U64 (wsize_size sz * j) + ptr) sz.
Proof.
  have hn := wsize_size_pos sz.
  have hnz : wsize_size sz ≠ 0%Z by Psatz.lia.
  move => /eqP /Zmod_divides [] // p hptr.
  rewrite /wunsigned CoqWord.word.addwE -!/(wunsigned _) Zplus_mod hptr -Zplus_mod.
  rewrite wunsigned_repr -/(wbase Uptr) (cut_wbase_Uptr sz).
  rewrite (Z.mul_comm _ (CoqWord.word.modulus _)) mod_pq_mod_q // (Z.mul_comm _ p) Z_mod_plus.
  2: Psatz.lia.
  by rewrite mod_pq_mod_q //; apply/eqP/Zmod_divides; eauto.
Qed.

Lemma is_align_no_overflow ptr sz :
  is_align ptr sz → no_overflow ptr (wsize_size sz).
Proof.
  rewrite /no_overflow => /eqP ha; apply/ZleP.
  have hn := wsize_size_pos sz.
  have hnz : wsize_size sz ≠ 0%Z by Psatz.lia.
  move: (wunsigned ptr) (wunsigned_range ptr) ha => {ptr} ptr.
  rewrite (cut_wbase_Uptr sz); set a := CoqWord.word.modulus _.
  move: (wsize_size sz) hn hnz => n hn hnz hr /Zmod_divides [] // q ?; subst ptr.
  cut (q + 1 <= a)%Z; Psatz.nia.
Qed.

Lemma is_align8 (ptr:pointer) : is_align ptr U8.
Proof. by rewrite wsize8 /= Z.mod_1_r. Qed.

Instance A : alignment :=
  Alignment is_align8 is_align_array is_align_no_overflow.

End Align.

Module MemoryI : MemoryT.

  Instance A : alignment := Align.A.

  Definition is_zalloc (m:Mz.t bool) (p:Z) := odflt false (Mz.get m p).

  Definition frames_size cur_frame (frames: seq Z) := 
    foldr Z.add 0%Z (cur_frame :: frames).

  Definition valid_frames (stk_ptr: pointer) cur_frame (frames: seq Z) := 
    all (fun p => 0 <=? p)%Z (cur_frame :: frames) && 
      (wunsigned stk_ptr + frames_size cur_frame frames <? (wbase U64))%Z.

  Record mem_ := {
    data      : Mz.t u8;
    alloc     : Mz.t bool;
    stk_low   : pointer;
    stk_ptr   : pointer;
    cur_frame : Z;       (* size of the current frame *)     
    frames    : seq Z;        (* size of the frame on the stack *)
    framesP   : valid_frames stk_ptr cur_frame frames;
    stk_ptrP  : 0 <= wunsigned stk_low <= wunsigned stk_ptr;
    stk_okP   : forall x, wunsigned stk_low <= x < wunsigned stk_ptr + frames_size cur_frame frames -> 
                   is_zalloc alloc x = (wunsigned stk_ptr <=? x);
  }.
 
  Definition mem := mem_.

  Definition is_alloc (m:mem) (p:pointer) (ws: wsize) := 
    all (fun i => is_zalloc m.(alloc) (wunsigned (p + wrepr U64 i))) (ziota 0 (wsize_size ws)).

  Lemma is_allocP m p ws : 
    reflect (forall i, 0 <= i < wsize_size ws -> 
               is_zalloc m.(alloc) (wunsigned (p + wrepr U64 i)))
           (is_alloc m p ws).
  Proof.
    apply: equivP; first by apply allP.
    by split => h i hi; apply h; move: hi; rewrite in_ziota !zify Z.add_0_l.
  Qed.

  Definition valid_pointer (m:mem) (p:pointer) (ws: wsize) := 
    is_align p ws && is_alloc m p ws.
 
  Definition add (p:pointer) (o:Z) := (p + wrepr U64  o)%R.

  Definition sub (p1 p2:pointer)  := wunsigned p1 - wunsigned p2.

  Definition uget (m:mem) (p:pointer) := odflt 0%R (Mz.get m.(data) (wunsigned p)).

  Definition uset (m:mem) (p:pointer) (w:u8) := 
    {| data      := Mz.set m.(data) (wunsigned p) w ;
       alloc     := m.(alloc);
       stk_low   := m.(stk_low);
       stk_ptr   := m.(stk_ptr);
       cur_frame := m.(cur_frame);
       frames    := m.(frames);
       framesP   := m.(framesP);
       stk_ptrP  := m.(stk_ptrP);
       stk_okP   := m.(@stk_okP);
    |}.    
  
  Definition valid m p ws := assert (valid_pointer m p ws) ErrAddrInvalid.

  Lemma add_sub p k: add p (sub k p) = k.
  Proof. rewrite /add /sub wrepr_sub !wrepr_unsigned; ssrring.ssring. Qed.

  Lemma sub_add m p s i t: valid m p s = ok t -> 0 <= i < wsize_size s -> sub (add p i) p = i.
  Proof. 
    rewrite /valid => /assertP; rewrite /valid_pointer => /andP [].
    move=> /is_align_no_overflow; rewrite /no_overflow !zify => ha _ hi.
    have ? := wunsigned_range p; rewrite /sub /add wunsigned_add; Psatz.lia.
  Qed.

  Lemma add_0 p: add p 0 = p.
  Proof. by rewrite /add wrepr0; ssrring.ssring. Qed.

  Lemma validw_uset m p v p' s : valid (uset m p v) p' s = valid m p' s.
  Proof. done. Qed.

  Lemma validrP m p s i t: 
    valid m p s = ok t ->
    0 <= i < wsize_size s ->  
    valid m (add p i) U8 = ok t.
  Proof.
    rewrite /valid /valid_pointer is_align8 /= andbC.
    by case: is_allocP => //= ha _ /ha; rewrite /is_alloc /= wrepr0 addr0 => ->; case: t.
  Qed.

  Lemma validw_validr m p s i v t k:
    valid m p s = ok t -> 
    0 <= i < wsize_size s ->
    valid (uset m (add p i) v) k U8 = if add p i == k then ok t else valid m k U8.
  Proof.
    rewrite /valid /valid_pointer is_align8 /=.
    case: andP => //= -[_ /is_allocP h] [<-] /h.
    by rewrite /is_alloc /= wrepr0 addr0 andbT; case:eqP => // <- ->.
  Qed.

  Lemma setP m z1 z2 v:
    uget (uset m z1 v) z2 = if z1 == z2 then v else uget m z2.
  Proof.
    by rewrite /uget /uset /= Mz.setP (eqtype.inj_eq (@wunsigned_inj _)); case: eqP.
  Qed.
 
  Instance CM : coreMem mem pointer := 
    CoreMem add_sub sub_add add_0 validw_uset validrP validw_validr setP.
  
  Definition read_mem (m: mem) (ptr: pointer) (ws: wsize) : exec (word ws) := 
    CoreMem.read m ptr ws.

  Definition bounded (z1 z2 z3: Z) := (z1 <=? z2) && (z2 <? z3).

  Definition write_mem (m: mem) (ptr:pointer) (ws:wsize) (v:word ws) := 
    CoreMem.write m ptr v.
  
  Lemma is_align_valid_pointer m p ws :
    is_align p ws -> 
    (forall k, 0 <= k < wsize_size ws -> valid_pointer m (p + wrepr U64 k) U8) ->
    valid_pointer m p ws.
  Proof.
    rewrite /valid_pointer /is_alloc=> -> /= h.
    by apply /allP => i; rewrite in_ziota !zify => /h /and3P [] _; rewrite wrepr0 addr0.
  Qed.

  Lemma addP p k: add p k = (p + wrepr U64 k)%R.
  Proof. done. Qed.

  Lemma readP m p s : read_mem m p s = CoreMem.read m p s. 
  Proof. done. Qed.

  Lemma writeP m p s (v:word s): write_mem m p v = CoreMem.write m p v.
  Proof. done. Qed.

  Definition top_stack (m:mem) := m.(stk_ptr).

  Fixpoint stack_aux (p:Z) (l:seq Z) : seq (Z * Z) := 
    match l with
    | [::] => [::]
    | z::l => (p,z) :: stack_aux (p+z) l
    end.

  Definition stack (m:mem) := 
    stack_aux (wunsigned m.(stk_ptr)) (m.(cur_frame) :: m.(frames)).

  Definition get_frame (m:mem) (p:pointer) := 
    let stack := stack m in
    let i := find (fun pz => pz.1 == wunsigned p) stack in
    ohead (drop i stack).

  Definition caller (m:mem) (p:pointer) := 
    omap (fun pz => wrepr U64 pz.1) (get_frame m p).

  Definition frame_size (m:mem) (p:pointer) := 
    omap fst (get_frame m p).

  Definition set_alloc b (m:Mz.t bool) (ptr sz:Z) := 
    foldl (fun m k => Mz.set m k b) m (ziota ptr sz).

  Lemma set_allocP b m p sz x :
    is_zalloc (set_alloc b m p sz) x = 
      if (p <=? x) && (x <? p + sz) then b else is_zalloc m x.
  Proof.
    rewrite /set_alloc -in_ziota; elim: ziota m => //= i l hrec m.
    rewrite in_cons hrec orbC; case: ifP => //= ?.
    by rewrite /is_zalloc Mz.setP eq_sym; case: ifP.
  Qed.

  Lemma decr_stk (low ptr:pointer) sz:
    bounded (wunsigned low) ((wunsigned ptr) - sz)%Z (wunsigned ptr) ->
    wunsigned (ptr - wrepr U64 sz)%R = wunsigned ptr - sz. 
  Proof.
    rewrite /bounded => /andP [] /ZleP ? /ZltP ?.
    rewrite wunsigned_sub //.
    by have := wunsigned_range ptr; have := wunsigned_range low; Psatz.lia. 
  Qed.

  Lemma framesP_alloc m sz: 
    bounded (wunsigned m.(stk_low)) ((wunsigned m.(stk_ptr)) - sz)%Z (wunsigned m.(stk_ptr)) ->
    valid_frames (m.(stk_ptr) - wrepr U64 sz)%R sz (m.(cur_frame) :: m.(frames)).
  Proof.
    move=> h;rewrite /valid_frames (decr_stk h).
    move: h;rewrite /bounded => /andP [] /ZleP ? /ZltP ?.
    have ? := m.(stk_ptrP); rewrite /valid_frames /=.
    have /ZleP -> /= : (0 <= sz)%Z by Psatz.lia.
    have /andP [/= -> /ZltP /=] := m.(framesP).
    rewrite /frames_size /= ?zify; first Psatz.lia.
  Qed.

  Lemma stk_ptrP_alloc (m:mem) sz: 
    bounded (wunsigned m.(stk_low)) (wunsigned m.(stk_ptr) - sz)%Z (wunsigned m.(stk_ptr)) ->
    0 <= (wunsigned m.(stk_low)) <= (wunsigned (m.(stk_ptr) - wrepr U64 sz)).
  Proof. 
    move=> h;rewrite (decr_stk h).
    by move/andP: h => [/ZleP ? /ZltP ?]; case : m.(stk_ptrP);auto. 
  Qed.

  Lemma stk_okP_alloc (m:mem) sz: 
    bounded (wunsigned m.(stk_low)) (wunsigned m.(stk_ptr) - sz)%Z (wunsigned m.(stk_ptr)) ->
    let newptr := (m.(stk_ptr) - wrepr U64 sz)%R in
    forall x, 
      wunsigned m.(stk_low) <= x < 
         wunsigned newptr + frames_size sz (m.(cur_frame)::m.(frames)) -> 
      is_zalloc (set_alloc true m.(alloc) (wunsigned newptr) sz) x = (wunsigned newptr <=? x).
  Proof. 
    move=> h;rewrite /= (decr_stk h) /frames_size /= => x ?.
    rewrite set_allocP; case: ifPn; rewrite !zify => ?.
    + by symmetry; apply/ZleP; Psatz.lia.
    rewrite m.(@stk_okP); last by rewrite /frames_size /=; Psatz.lia.
    move: h;rewrite /bounded !zify.
    case: ZleP;case: ZleP => //??; Psatz.lia. 
  Qed.

  Definition alloc_stack (m:mem) (sz:Z) : exec mem :=
    let t := 
     bounded (wunsigned m.(stk_low)) (wunsigned m.(stk_ptr) - sz)%Z (wunsigned m.(stk_ptr)) in
    let newptr := (m.(stk_ptr) - wrepr U64 sz)%R in
    match Sumbool.sumbool_of_bool t with
    | right _ => Error ErrStack
    | left h  =>
      ok
        {| data      := m.(data);
           alloc     := set_alloc true m.(alloc) (wunsigned newptr) sz;
           stk_low   := m.(stk_low);
           stk_ptr   := newptr;
           cur_frame := sz; 
           frames    := m.(cur_frame) :: m.(frames);
           framesP   := framesP_alloc h; 
           stk_ptrP  := stk_ptrP_alloc h;
           stk_okP   := stk_okP_alloc h;
        |}
    end.

  Lemma frames_size_pos m : 0 <= foldr Z.add 0 (frames m).
  Proof.
    have /andP [/= /andP [] /ZleP h1 h2 _]:= m.(framesP); rewrite /frames_size /=.
    by elim : (frames m) h2 => /= [_ | i l hrec /andP [] /ZleP ? /hrec]; Psatz.lia.  
  Qed.

  Lemma incr_stk (m:mem) :
    wunsigned (stk_ptr m + wrepr U64 (cur_frame m))%R = 
     wunsigned (stk_ptr m) + cur_frame m. 
  Proof.
    have := m.(framesP); have := @frames_size_pos m.
    rewrite /valid_frames /frames_size /= => ? /andP [] /andP [] /ZleP ? _ /ZltP ?.
    have ? := wunsigned_range (stk_ptr m).
    by rewrite wunsigned_add; Psatz.lia. 
  Qed.

  Lemma framesP_free m sz fr : 
    m.(frames) = sz :: fr ->  
    valid_frames (m.(stk_ptr) + wrepr U64 m.(cur_frame))%R sz fr.
  Proof.
    move=> heq;have := m.(framesP); rewrite /valid_frames incr_stk heq /frames_size /=.
    move=> /andP [] /and3P [] /ZleP h1 h2 ->.
    by rewrite h2 => /ZltP /= ?; apply /ZltP; move /ZleP: h2 => h2; Psatz.lia. 
  Qed.

  Lemma stk_ptrP_free (m:mem): 
     0 <= wunsigned m.(stk_low) <= wunsigned (m.(stk_ptr) + wrepr U64 m.(cur_frame)).
  Proof. 
    rewrite incr_stk.
    have := m.(framesP); have:= m.(stk_ptrP).
    by rewrite /valid_frames /= !zify /frames_size /= => *; Psatz.lia. 
  Qed.

  Lemma stk_okP_free (m:mem) sz fr: 
    m.(frames) = sz :: fr ->  
    let newptr := (m.(stk_ptr) + wrepr U64 m.(cur_frame))%R in
    forall x, 
      wunsigned m.(stk_low) <= x < wunsigned newptr + frames_size sz fr -> 
      is_zalloc (set_alloc false m.(alloc) (wunsigned m.(stk_ptr)) m.(cur_frame)) x =
              (wunsigned newptr <=? x).
  Proof. 
    move=> h /=; rewrite incr_stk => /= x hx.
    rewrite set_allocP m.(@stk_okP). 
    + have /andP /= [/andP [/ZleP ??] _ ] := m.(framesP).
      case: ifPn;rewrite !zify => h1.
      + symmetry;apply /negP => /ZleP; Psatz.lia.
      case: ZleP; case:ZleP => // ??; Psatz.lia.
    by move: hx; rewrite /frames_size h /=; Psatz.lia.
  Qed.

  Definition free_stack (m:mem) (sz:Z) :=
    match m.(frames) as f return m.(frames) = f -> mem with
    | [::] => fun _ => m
    | sz :: fr => 
      fun (h:m.(frames) = sz::fr) =>
        {| data      := m.(data);
           alloc     := set_alloc false m.(alloc) (wunsigned m.(stk_ptr)) m.(cur_frame);
           stk_low   := m.(stk_low);
           stk_ptr   :=(m.(stk_ptr) + wrepr U64 m.(cur_frame))%R;
           cur_frame := sz; 
           frames    := fr;
           framesP   := framesP_free h; 
           stk_ptrP  := stk_ptrP_free m;
           stk_okP   := stk_okP_free h;
        |}
    end (erefl _).

  Definition init_alloc (s: seq (pointer * Z)) := 
    foldl (λ (a : Mz.t bool) (pz : u64 * Z), set_alloc true a (wunsigned pz.1) pz.2)
         (Mz.empty bool) s.

  Lemma stk_okP_init_alloc s x : 
    0 <= x < 0 + frames_size 0 [::] → is_zalloc (init_alloc s) x = (0 <=? x).
  Proof. by rewrite /frames_size /=; Psatz.lia. Qed.

  Definition init_mem (s: seq (pointer * Z)) : mem :=
    {| data := Mz.empty _;
       alloc := foldl (fun a pz => set_alloc true a (wunsigned pz.1) pz.2) (Mz.empty _) s;
       stk_low := 0%R;
       stk_ptr := 0%R;
       cur_frame := 0;
       frames := [::];
       framesP := erefl _;
       stk_ptrP := conj (Z.le_refl _) (Z.le_refl _);
       stk_okP := @stk_okP_init_alloc s;|}.

  Lemma valid_pointerP m p s: reflect (is_ok (valid m p s)) (valid_pointer m p s).
  Proof. rewrite /valid;case: valid_pointer => //=; apply idP. Qed.

  Lemma readV (m:mem) p s: reflect (exists v, read_mem m p s = ok v) (valid_pointer m p s).
  Proof. 
    rewrite /read_mem /CoreMem.read /= /valid.
    by (case: valid_pointer => /=; constructor) => [ | []//]; eauto.
  Qed.

  Lemma writeV m p s (v:word s):
    reflect (exists m', write_mem m p v = ok m') (valid_pointer m p s).
  Proof.
    rewrite /write_mem /CoreMem.write /= /valid.
    by (case: valid_pointer => /=; constructor) => [ | []//]; eauto.
  Qed.

  Lemma read_mem_error m p s e: read_mem m p s = Error e -> e = ErrAddrInvalid.
  Proof.
    by rewrite /read_mem /CoreMem.read /= /valid; case: valid_pointer => [|[<-]]. 
  Qed.

  Lemma valid_align m p s: valid_pointer m p s -> is_align p s.
  Proof. by move=> /andP []. Qed.

  Instance M : memory mem :=
    Memory read_mem write_mem valid_pointer 
      top_stack caller frame_size alloc_stack free_stack init_mem.

  Lemma write_memE m m' p s (v:word s): 
    write_mem m p v = ok m' ->
    validw m p s = ok tt /\ m' = CoreMem.uwrite m p v.
  Proof.
    by rewrite /write_mem /CoreMem.write /= /valid /assert; case:ifP => //= _ [<-].
  Qed.

  Lemma alloc_uwrite m p s (v:word s): 
    alloc (CoreMem.uwrite m p v) = alloc m.
  Proof. by rewrite /CoreMem.uwrite; elim: ziota m => //= ?? hrec ?;rewrite hrec. Qed.

  Lemma write_valid m m' p s (v:word s) p' s':
    write_mem m p v = ok m' ->
    valid_pointer m' p' s' = valid_pointer m p' s'.
  Proof.
    move=> /write_memE [hv ->].
    rewrite /valid_pointer /validr /= /is_alloc; f_equal.
    by apply eq_in_all => i; rewrite alloc_uwrite.
  Qed.

  Lemma write_read8 m m' p ws (v: word ws) k :
    write_mem m p v = ok m' ->
    read_mem m' k U8 = 
      let i := wunsigned k - wunsigned p in
      if (0 <=? i) && (i <? wsize_size ws) then ok (LE.wread8 v i)
      else read_mem m k U8.
  Proof. apply: CoreMem.write_read8. Qed.
   
  Lemma writeP_eq m m' p s (v :word s):
    write_mem m p v = ok m' ->
    read_mem m' p s = ok v.
  Proof. 
    move=> hw; rewrite /read_mem /CoreMem.read /= /valid.
    rewrite (write_valid _ _ hw).
    (case: (writeV m p v); rewrite hw) => [[m1 _] /= | []]; last by eauto.
    by rewrite (CoreMem.writeP_eq hw) LE.decodeK.
  Qed.

  Lemma writeP_neq m m' p s (v :word s) p' s':
    write_mem m p v = ok m' ->
    disjoint_range p s p' s' ->
    read_mem m' p' s' = read_mem m p' s'.
  Proof.
    rewrite /read_mem /CoreMem.read /= /valid => hw [ /ZleP hno /ZleP hno' hd].
    rewrite (write_valid p' s' hw); case:valid_pointer => //=.
    rewrite (CoreMem.writeP_neq hw) // => i i' hi hi'.
    rewrite /= /add => heq. 
    have : wunsigned (p + wrepr U64 i)%R = wunsigned (p' + wrepr U64 i')%R by rewrite heq.
    have hp := wunsigned_range p; have hp' := wunsigned_range p'.
    rewrite !wunsigned_add; Psatz.lia.
  Qed.

  Lemma read_write_any_mem m1 m1' pr szr pw szw (vw:word szw) m2 m2':
    valid_pointer m1 pr szr ->
    read_mem m1 pr szr = read_mem m1' pr szr ->
    write_mem m1 pw vw = ok m2 ->
    write_mem m1' pw vw = ok m2' ->
    read_mem m2 pr szr = read_mem m2' pr szr.
  Proof.
    move=> hv hr hw hw'; move: hr; rewrite /read_mem /CoreMem.read /= /valid.
    rewrite (write_valid _ _ hw) (write_valid _ _ hw') hv /=.
    case: valid_pointer => //= h; have {h}/eqP/CoreMem.uread_decode h := ok_inj h; do 2 f_equal.
    apply /eqP /CoreMem.ureadP => i hin.
    by rewrite (CoreMem.write_uget _ hw) (CoreMem.write_uget _ hw') h.
  Qed.

(* -------------------------------------------------------------------- *)
 (* Lemma ass_mod m m' sz: alloc_stack m sz = ok m' -> wunsigned (top_stack m') + sz <= wbase Uptr.
  Proof.
    rewrite /alloc_stack; case: Sumbool.sumbool_of_bool => // h [<-] /=.
    rewrite (decr_stk h); have := wunsigned_range (stk_ptr m); Psatz.lia.
  Qed.

  Lemma is_zalloc_set b m n sz p: is_zalloc (set_alloc b m n sz) p = 
    if (n <=? p) && (p <? n + sz) then b else is_zalloc m p.
  Proof.
    rewrite /is_zalloc /set_alloc -in_ziota.
    elim: ziota m => //= i l hrec m;rewrite hrec Mz.setP in_cons orbC.
    by case: ifPn => //= ?; rewrite eq_sym; case:ifP.
  Qed.

(* TODO: move this *)
  Lemma no_overflow_add z p i : 0 <= z -> no_overflow p z -> 0 <= i < z ->  wunsigned (p + wrepr U64 i) = wunsigned p + i.
  Proof.
    rewrite /no_overflow zify => h0z ho hi; rewrite wunsigned_add //.
    have := wunsigned_range p; Psatz.lia.
  Qed.

  Lemma ass_valid  m sz m' p s:
    alloc_stack m sz = ok m'->
    valid_pointer m' p s =
      valid_pointer m p s || (between (top_stack m') sz p s && is_align p s).
  Proof.
    rewrite /alloc_stack; case: Sumbool.sumbool_of_bool => // h [<-].
    rewrite /valid_pointer; case: (@idP (is_align _ _)) => ha /=; last by rewrite andbF.
    rewrite andbT /is_alloc /=; set a1 := (t in _ = t || _); case: (@idP a1); rewrite /a1 {a1} /=.
    + by apply: sub_all => k; rewrite is_zalloc_set; case: ifP.
    move=> /negP /allPn [i1 hi1 hai1]; have hpo := is_align_no_overflow ha.
    case: (@idP (between _ _ _ _)); rewrite /between (decr_stk h) !zify => ?.
    + apply /allP => i2; rewrite in_ziota !zify is_zalloc_set Z.add_0_l => hi2.
      rewrite (no_overflow_add _ hpo hi2) //.
      by case: ifPn => //; rewrite !zify; Psatz.lia.
    apply /negbTE /allPn; exists i1 => //.
    rewrite is_zalloc_set; case: ifP => //.
    move: hi1; rewrite in_ziota !zify => hi1; rewrite (no_overflow_add _ hpo hi1) //.
*)

  Lemma alloc_stackP m m' sz :
    alloc_stack m sz = ok m' -> alloc_stack_spec m sz m'.
  Proof.
  Admitted.

  Lemma write_mem_stable m m' p s (v:word s) : 
    write_mem m p v = ok m' -> stack_stable m m'.
  Proof.
  Admitted.

  Lemma free_stackP : forall m sz,
    frame_size m (top_stack m) = Some sz ->
    free_stack_spec m sz (free_stack m sz).
  Proof.
  Admitted.

End MemoryI.
