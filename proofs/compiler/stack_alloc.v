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

(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import Coq.Logic.Eqdep_dec.
Require Import strings word utils gen_map type var expr low_memory sem.
Require Import constant_prop compiler_util allocation byteset.
Require Import ZArith.
Import x86_variables.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

Definition size_of (t:stype) :=
  match t with
  | sword sz => wsize_size sz
  | sarr n   => Zpos n
  | sbool | sint => 1%Z
  end.

Local
Definition cerror {A} msg :=
  @cerror (Cerr_stk_alloc msg) A.

Local
Definition cferror {A} fn msg :=
  @Error _ A (Ferr_fun fn (Cerr_stk_alloc msg)).

Definition slot := var.

Notation size_slot s := (size_of s.(vtype)).

Record region :=
  { r_slot : slot;        (* the name of the region        *)
      (* the size of the region is encoded in the type of [r_slot] *)
    r_align : wsize;      (* the alignment of the region   *)
    r_writable : bool;    (* the region is writable or not *)
  }.

Definition region_beq (r1 r2:region) :=
  [&& r1.(r_slot)     == r2.(r_slot), 
      r1.(r_align)    == r2.(r_align) &
      r1.(r_writable) == r2.(r_writable)].

Definition region_same (r1 r2:region) :=
  (r1.(r_slot) == r2.(r_slot)).

Lemma region_axiom : Equality.axiom region_beq.
Proof.
  rewrite /region_beq => -[xs1 xa1 xw1] [xs2 xa2 xw2].
  by apply:(iffP and3P) => /= [[/eqP -> /eqP -> /eqP ->] | [-> -> ->]].
Qed.

Definition region_eqMixin := Equality.Mixin region_axiom.
Canonical  region_eqType  := Eval hnf in EqType region region_eqMixin.

Module CmpR.

  Definition t := [eqType of region].

  Definition cmp (r1 r2: t) := 
    Lex (bool_cmp r1.(r_writable) r2.(r_writable))
     (Lex (wsize_cmp r1.(r_align) r2.(r_align))
          (var_cmp r1.(r_slot) r2.(r_slot))).

  Instance cmpO : Cmp cmp.
  Proof.
    constructor => [x y | y x z c | [???] [???]]; rewrite /cmp !Lex_lex.
    + by repeat (apply lex_sym; first by apply cmp_sym); apply cmp_sym.
    + by repeat (apply lex_trans=> /=; first by apply cmp_ctrans); apply cmp_ctrans.
    move=> /lex_eq [] /= h1 /lex_eq [] /= h2 h3.
    by rewrite (cmp_eq h1) (cmp_eq h2) (cmp_eq h3).
  Qed.

End CmpR.

Module Mr := Mmake CmpR.

(* ------------------------------------------------------------------ *)
Record zone := {
  z_ofs : Z;
  z_len : Z;
}.

Scheme Equality for zone.

Lemma zone_eq_axiom : Equality.axiom zone_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_zone_dec_bl.
  by apply: internal_zone_dec_lb.
Qed.

Definition zone_eqMixin := Equality.Mixin zone_eq_axiom.
Canonical  zone_eqType  := EqType zone zone_eqMixin.

(*
Module CmpZ.

  Definition t := [eqType of zone].

  Definition cmp (z1 z2: t) := 
    Lex (Z.compare z1.(z_ofs) z2.(z_ofs))
        (Z.compare z1.(z_len) z2.(z_len)).

  Instance cmpO : Cmp cmp.
  Proof.
    constructor => [x y | y x z c | [??] [??]]; rewrite /cmp !Lex_lex.
    + by apply lex_sym; apply cmp_sym.
    + by apply lex_trans=> /=; apply cmp_ctrans.
    move=> /lex_eq [] /= h1 h2.
    by rewrite (cmp_eq h1) (cmp_eq h2).
  Qed.

End CmpZ.

Module Mz := Mmake (CmpZ).
*)

Definition disjoint_zones z1 z2 := 
  (((z1.(z_ofs) + z1.(z_len))%Z <= z2.(z_ofs)) || 
   ((z2.(z_ofs) + z2.(z_len))%Z <= z1.(z_ofs)))%CMP.

(* ------------------------------------------------------------------ *)
(* A zone inside a region. *)
Record sub_region := {
    sr_region : region;
    sr_zone  : zone;
  }.

Definition sub_region_beq sr1 sr2 := 
  (sr1.(sr_region) == sr2.(sr_region)) && (sr1.(sr_zone) == sr2.(sr_zone)).

Lemma sub_region_eq_axiom : Equality.axiom sub_region_beq.
Proof.
  rewrite /sub_region_beq => -[mp1 sub1] [mp2 sub2].
  by apply:(iffP andP) => /= [[/eqP -> /eqP ->] | [-> ->]].
Qed.

Definition sub_region_eqMixin := Equality.Mixin sub_region_eq_axiom.
Canonical sub_region_eqType := EqType sub_region sub_region_eqMixin.

(*
Module CmpSr.
  Definition t := [eqType of sub_region].

  Definition cmp (sr1 sr2: t) := 
    Lex (CmpR.cmp sr1.(sr_region) sr2.(sr_region))
        (CmpZ.cmp sr1.(sr_zone) sr2.(sr_zone)).

  Instance cmpO : Cmp cmp.
  Proof.
    constructor => [x y | y x z c | [??] [??]]; rewrite /cmp !Lex_lex.
    + by apply lex_sym; apply cmp_sym.
    + by apply lex_trans=> /=; apply cmp_ctrans.
    move=> /lex_eq [] /= h1 h2.
    by rewrite (cmp_eq h1) (cmp_eq h2).
  Qed.

End CmpSr.

Module Msr := Mmake(CmpSr).
*)

(* ------------------------------------------------------------------ *)
(* idea: could we use a gvar instead of var & v_scope? *)
Variant ptr_kind_init :=
| PIdirect of var & zone & v_scope
| PIregptr of var
| PIstkptr of var & zone & var.

Variant ptr_kind :=
| Pdirect of var & Z & wsize & zone & v_scope
| Pregptr of var
| Pstkptr of var & Z & wsize & zone & var.

Record param_info := { 
  pp_ptr      : var;
  pp_writable : bool;
  pp_align    : wsize;
}.

Record pos_map := {
  vrip    : var;
  vrsp    : var;
  globals : Mvar.t (Z * wsize);
  locals  : Mvar.t ptr_kind;
  vnew    : Sv.t;
}.

Definition check_align (sr:sub_region) ws :=
  Let _ := assert (ws <= sr.(sr_region).(r_align))%CMP
                  (Cerr_stk_alloc "unaligned offset") in
  assert (Z.land sr.(sr_zone).(z_ofs) (wsize_size ws - 1) == 0)%Z
               (Cerr_stk_alloc "unaligned sub offset").

Definition writable (r:region) := 
  assert r.(r_writable)
   (Cerr_stk_alloc "Cannot write a constant pointer").

Module Region.

Definition bytes_map := Mvar.t ByteSet.t.

Record region_map := {
  var_region : Mvar.t sub_region; (* The region where the value is initialy stored            *)
  region_var :> Mr.t bytes_map;     (* The set of source variables whose value is in the region *)
    (* region -> var -> ByteSet.t *)
}.

Definition empty_bytes_map := Mvar.empty ByteSet.t.

Definition empty_zone_map := Mz.empty bytes_map.

Definition empty := {|
  var_region := Mvar.empty _;
  region_var := Mr.empty bytes_map;
|}.

Definition get_sub_region (rmap:region_map) (x:var) :=
  match Mvar.get rmap.(var_region) x with
  | Some sr => ok sr
  | None => cerror "no associated region"
  end.

Definition get_bytes_map (r:region) rv : bytes_map :=
  odflt empty_bytes_map (Mr.get rv r).

Definition get_bytes (x:var) (bytes_map:bytes_map) :=
  odflt ByteSet.empty (Mvar.get bytes_map x).

Definition interval_of_zone z := 
  {| imin := z.(z_ofs); imax := z.(z_ofs) + z.(z_len) |}.

Definition get_var_bytes rv r x :=
  let bm := get_bytes_map r rv in
  let bytes := get_bytes x bm in
  bytes.

(* Returns the sub-zone of [z] starting at offset [ofs] and of length [len].
   The offset [z] can be None, meaning its exact value is not known. In this
   case, the full zone [z] is returned. This is a safe approximation.
*)
Definition sub_zone_at_ofs z ofs len := 
  match ofs with
  | None => z
  | Some ofs => {| z_ofs := z.(z_ofs) + ofs; z_len := len |}
  end.

Definition sub_region_at_ofs sr ofs len :=
  {| sr_region := sr.(sr_region);
     sr_zone   := sub_zone_at_ofs sr.(sr_zone) ofs len
  |}.

Definition check_valid (rmap:region_map) (x:var) ofs len :=
  (* we get the bytes associated to variable [x] *)
  Let sr := get_sub_region rmap x in
  let bytes := get_var_bytes rmap sr.(sr_region) x in
  let sub_ofs  := sub_zone_at_ofs sr.(sr_zone) ofs len in
  let isub_ofs := interval_of_zone sub_ofs in
  (* we check if [isub_ofs] is a subset of one of the intervals of [bytes] *)
  Let _   := assert (ByteSet.mem bytes isub_ofs)
                    (Cerr_stk_alloc "check_valid: the region is partial") in
  ok {| sr_region := sr.(sr_region); sr_zone := sub_ofs |}.

Definition clear_bytes i bytes := ByteSet.remove bytes i.
(* TODO: check optim
  let bytes := ByteSet.remove bytes i in
  if ByteSet.is_empty bytes then None else Some bytes.
*)

Definition clear_bytes_map i (bm:bytes_map) :=
  Mvar.map (clear_bytes i) bm.
(* TODO: if optim above, optim below
  let bm := Mvar.filter_map (clear_bytes i) bm in
  if Mvar.is_empty bm then None else Some bm.
*)

Definition set_pure_bytes rv (x:var) sr ofs len :=
  let z     := sr.(sr_zone) in
  let z1    := sub_zone_at_ofs z ofs len in
  let i     := interval_of_zone z1 in
  let bm    := get_bytes_map sr.(sr_region) rv in
  let bytes := if ofs is Some _ then ByteSet.add i (get_bytes x bm)
               else get_bytes x bm
  in
  (* clear all bytes corresponding to sub1 *)
  let bm := clear_bytes_map i bm in
  (* set the bytes *)
  let bm := Mvar.set bm x bytes in
  Mr.set rv sr.(sr_region) bm.

Definition set_bytes rv (x:var) sr (ofs : option Z) (len : Z) :=
  Let _     := writable sr.(sr_region) in
  ok (set_pure_bytes rv x sr ofs len).

Definition set_sub_region rmap (x:var) sr (ofs : option Z) (len : Z) :=
  Let rv := set_bytes rmap x sr ofs len in
  ok {| var_region := Mvar.set rmap.(var_region) x sr;
        region_var := rv |}.

Definition sub_region_stkptr s ws z :=
  let r := {| r_slot := s; r_align := ws; r_writable := true |} in
  {| sr_region := r; sr_zone := z |}.

Definition set_stack_ptr (rmap:region_map) s ws z (x':var) :=
  let sr := sub_region_stkptr s ws z in
  Let rv := set_bytes rmap x' sr (Some 0)%Z (wsize_size Uptr) in
  ok {| var_region := rmap.(var_region);
        region_var := rv |}.

(* TODO: fusion with check_valid ? *)
Definition check_stack_ptr (rmap:region_map) s ws z x' :=
  let sr := sub_region_stkptr s ws z in
  let z := sub_zone_at_ofs z (Some 0)%Z (wsize_size Uptr) in
  let i := interval_of_zone z in
  let bytes := get_var_bytes rmap sr.(sr_region) x' in
  Let _   := assert (ByteSet.mem bytes i)
                    (Cerr_stk_alloc "check_stack_ptr: the region is partial") in
  ok tt.

(* Precondition size_of x = ws && length sr.sr_zone = wsize_size ws *)
Definition set_word rmap (x:var) sr ws :=
  Let _ := check_align sr ws in
  set_sub_region rmap x sr (Some 0)%Z (size_slot x).

(* If we write to array [x] at offset [ofs], we invalidate the corresponding
   memory zone for the other variables, and mark it as valid for [x].
   The offset [ofs] can be None, meaning its exact value is not known. In this
   case, the full zone [z] associated to array [x] is invalidated for the
   other variables, and remains the zone associated to [x]. It is a safe
   approximation.
*)
(* [set_word], [set_stack_ptr] and [set_arr_word] could be factorized? *)
Definition set_arr_word (rmap:region_map) (x:var) ofs ws :=
  Let sr := get_sub_region rmap x in
  Let _ := check_align sr ws in
  set_sub_region rmap x sr ofs (wsize_size ws).

(* TODO: verify that the right len is [size_slot x], not sr.(sr_zone).(z_len) !!! *)
Definition set_arr_call rmap x sr := set_sub_region rmap x sr (Some 0)%Z (size_slot x).

Definition set_arr_sub (rmap:region_map) (x:var) ofs len sr_from :=
  Let sr := get_sub_region rmap x in
  let z := sr.(sr_zone) in
  let sub_ofs := {| z_ofs := z.(z_ofs) + ofs; z_len := len |} in
  let bm := get_bytes_map sr.(sr_region) rmap in
  let bytes := get_bytes x bm in
  Let _ := assert (region_same sr.(sr_region) sr_from.(sr_region))
                  (Cerr_stk_alloc "set array: source and destination are not equal") in
  Let _ := assert (sub_ofs == sr_from.(sr_zone))
                  (Cerr_stk_alloc "set array: zones are not equal") in
  let bm := Mvar.set bm x (ByteSet.add (interval_of_zone sub_ofs) bytes) in
  ok {| var_region := rmap.(var_region); 
        region_var := Mr.set rmap.(region_var) sr.(sr_region) bm |}.

(* identical to [set_sub_region], except clearing
   TODO: fusion with set_arr_sub ? not sure its worth
*)
Definition set_move (rmap:region_map) (x:var) sr :=
  let z := sr.(sr_zone) in
  let i := interval_of_zone z in
  let bm := get_bytes_map sr.(sr_region) rmap in
  let bm := Mvar.set bm x (ByteSet.full i) in
  {| var_region := Mvar.set rmap.(var_region) x sr;
     region_var := Mr.set rmap.(region_var) sr.(sr_region) bm |}.

Definition set_arr_init rmap x sr := set_move rmap x sr.

Definition set_full rmap x r := 
  let len := size_slot x in
  let z := {| z_ofs := 0; z_len := len |} in
  let sr := {| sr_region := r; sr_zone := z |} in
  set_move rmap x sr.

Definition incl_bytes_map (_r: region) (bm1 bm2: bytes_map) := 
  Mvar.incl (fun x => ByteSet.subset) bm1 bm2.

Definition incl (rmap1 rmap2:region_map) :=
  Mvar.incl (fun x r1 r2 => r1 == r2) rmap1.(var_region) rmap2.(var_region) &&
  Mr.incl incl_bytes_map rmap1.(region_var) rmap2.(region_var).

Definition merge_bytes (x:var) (bytes1 bytes2: option ByteSet.t) := 
  match bytes1, bytes2 with
  | Some bytes1, Some bytes2 => 
    let bytes := ByteSet.inter bytes1 bytes2 in
    if ByteSet.is_empty bytes then None
    else Some bytes
  | _, _ => None
  end.

Definition merge_bytes_map (_r:region) (bm1 bm2: option bytes_map) :=
  match bm1, bm2 with
  | Some bm1, Some bm2 => 
    let bm := Mvar.map2 merge_bytes bm1 bm2 in
    if Mvar.is_empty bm then None
    else Some bm
  | _, _ => None
  end.

Definition merge (rmap1 rmap2:region_map) := 
  {| var_region := 
       Mvar.map2 (fun _ or1 or2 =>
        match or1, or2 with
        | Some r1, Some r2 => if r1 == r2 then or1 else None
        | _, _ => None
        end) rmap1.(var_region) rmap2.(var_region);
     region_var := Mr.map2 merge_bytes_map rmap1.(region_var) rmap2.(region_var) |}.

End Region.

Import Region.

Definition mul := Papp2 (Omul (Op_w Uptr)).
Definition add := Papp2 (Oadd (Op_w Uptr)).

Definition cast_word e := 
  match e with
  | Papp1 (Oint_of_word U64) e1 => e1
  | _  => cast_ptr e
  end.

Definition mk_ofs aa ws e1 ofs := 
  let sz := mk_scale aa ws in
  if is_const e1 is Some i then 
    cast_const (i * sz + ofs)%Z
  else 
    add (mul (cast_const sz) (cast_word e1)) (cast_const ofs).

Definition mk_ofsi aa ws e1 := 
  if is_const e1 is Some i then Some (i * (mk_scale aa ws))%Z
  else None.

Section Section.

Variables (pmap:pos_map).

Section ALLOC_E.

Variables (rmap: region_map).

Definition get_global (x:var) := 
  match Mvar.get pmap.(globals) x with
  | None => cerror "unallocated global variable: please report"
  | Some z => ok z
  end.

Definition get_local (x:var) := Mvar.get pmap.(locals) x.

Definition check_diff (x:var) :=
  if Sv.mem x pmap.(vnew) then cerror "the code write new variables, please report"
  else ok tt.

Definition check_var (x:var) := 
  match get_local x with
  | None => ok tt
  | Some _ => cerror "not a reg variable"
  end.

Inductive vptr_kind := 
  | VKglob of Z * wsize
  | VKptr  of ptr_kind.

Definition var_kind := option vptr_kind.

Definition with_var xi x := 
  {| v_var := x; v_info := xi.(v_info) |}.

Definition base_ptr sc :=
  match sc with
  | Slocal => pmap.(vrsp)
  | Sglobal => pmap.(vrip)
  end.

Definition mk_addr_ptr x aa ws (pk:ptr_kind) (e1:pexpr) := 
  match pk with
  | Pdirect _ ofs _ z sc => ok (with_var x (base_ptr sc), mk_ofs aa ws e1 (ofs + z.(z_ofs)))
  | Pregptr p            => ok (with_var x p,             mk_ofs aa ws e1 0)
  | Pstkptr _ _ _ _ _    => cerror "stack pointer in expression"
  end.

Definition mk_addr x aa ws (pk:vptr_kind) (e1:pexpr) := 
  match pk with
  | VKglob zws => ok (with_var x pmap.(vrip), mk_ofs aa ws e1 zws.1)
  | VKptr pk => mk_addr_ptr x aa ws pk e1
  end.

Definition get_var_kind x :=
  let xv := x.(gv) in
  if is_glob x then
    Let z := get_global xv in
    ok (Some (VKglob z))
  else 
    ok (omap VKptr (get_local xv)).

(* TODO: factorize with [set_full] ? probably not worth *)
Definition sub_region_glob x ws :=
  let r := {| r_slot := x; r_align := ws; r_writable := false |} in
  let z := {| z_ofs := 0; z_len := size_slot x |} in
  {| sr_region := r; sr_zone := z |}.

Definition check_vpk rmap (x:var) vpk ofs len :=
  match vpk with
  | VKglob (_, ws) =>
    let sr := sub_region_glob x ws in
    ok (sub_region_at_ofs sr ofs len)
  | VKptr _pk => 
    check_valid rmap x ofs len
  end.

Definition check_vpk_word rmap x vpk ofs ws :=
  Let sr := check_vpk rmap x vpk ofs (wsize_size ws) in
  check_align sr ws.

Fixpoint alloc_e (e:pexpr) := 
  match e with
  | Pconst _ | Pbool _ | Parr_init _ => ok e
  | Pvar   x =>
    let xv := x.(gv) in
    Let vk := get_var_kind x in
    match vk with
    | None => ok e
    | Some vpk => 
      if is_word_type (vtype xv) is Some ws then
        Let _ := check_vpk_word rmap xv vpk (Some 0%Z) ws in
        Let pofs := mk_addr xv AAdirect ws vpk (Pconst 0) in
        ok (Pload ws pofs.1 pofs.2)
      else cerror "not a word variable in expression, please report"
    end

  | Pget aa ws x e1 =>
    let xv := x.(gv) in
    Let e1 := alloc_e e1 in
    Let vk := get_var_kind x in
    match vk with
    | None => ok (Pget aa ws x e1)
    | Some vpk =>
      let ofs := mk_ofsi aa ws e1 in
      Let _ := check_vpk_word rmap xv vpk ofs ws in
      Let pofs := mk_addr xv aa ws vpk e1 in
      ok (Pload ws pofs.1 pofs.2)
    end             
  | Psub aa ws len x e1 =>
    cerror "Psub"

  | Pload ws x e1 =>
    Let _ := check_var x in
    Let e1 := alloc_e e1 in
    ok (Pload ws x e1)

  | Papp1 o e1 =>
    Let e1 := alloc_e e1 in
    ok (Papp1 o e1)
   
  | Papp2 o e1 e2 =>
    Let e1 := alloc_e e1 in
    Let e2 := alloc_e e2 in
    ok (Papp2 o e1 e2)

  | PappN o es => 
    Let es := mapM alloc_e es in
    ok (PappN o es)  

  | Pif t e e1 e2 =>
    Let e := alloc_e e in
    Let e1 := alloc_e e1 in
    Let e2 := alloc_e e2 in
    ok (Pif t e e1 e2)
  end.

  Definition alloc_es := mapM alloc_e.

End ALLOC_E.

Definition sub_region_direct x align sc z :=
  let r := {| r_slot := x; r_align := align; r_writable := sc != Sglob |} in
  {| sr_region := r; sr_zone := z |}.

Definition sub_region_stack x align z :=
  sub_region_direct x align Slocal z.

Definition sub_region_pk pk :=
  match pk with
  | Pdirect x ofs align sub Slocal => ok (sub_region_stack x align sub)
  | _ => cerror "not a pointer to stack: please report"
  end.

Definition alloc_lval (rmap: region_map) (r:lval) (ty:stype) :=
  match r with
  | Lnone _ _ => ok (rmap, r)

  | Lvar x =>
    (* TODO: could we remove this [check_diff] and use an invariant in the proof instead? *)
    Let _ := check_diff x in
    match get_local x with
    | None => ok (rmap, r)
    | Some pk => 
      if is_word_type (vtype x) is Some ws then 
        if ty == sword ws then 
          Let pofs := mk_addr_ptr x AAdirect ws pk (Pconst 0) in
          Let sr   := sub_region_pk pk in
          let r := Lmem ws pofs.1 pofs.2 in
          Let rmap := Region.set_word rmap x sr ws in
          ok (rmap, r)
        else cerror "invalid type for assignment"
      else cerror "not a word variable in assignment"
    end

  | Laset aa ws x e1 =>
    (* TODO: could we remove this [check_diff] and use an invariant in the proof instead? *)
    Let _ := check_diff x in
    Let e1 := alloc_e rmap e1 in
    match get_local x with
    | None => ok (rmap, Laset aa ws x e1)
    | Some pk => 
      let ofs := mk_ofsi aa ws e1 in 
      Let rmap := set_arr_word rmap x ofs ws in
      Let pofs := mk_addr_ptr x aa ws pk e1 in
      let r := Lmem ws pofs.1 pofs.2 in
      ok (rmap, r)
    end   
  | Lasub aa ws len x e1 =>
    cerror "Lasub"
  | Lmem ws x e1 =>
    Let _ := check_var x in
    Let e1 := alloc_e rmap e1 in
    ok (rmap, Lmem ws x e1)
  end.

Definition nop := Copn [::] AT_none Onop [::]. 

Definition lea_ptr x y ofs := 
  Copn [::x] AT_none (Ox86 (LEA Uptr)) [:: add y (cast_const ofs)].

Definition mov_ptr x y :=
  Copn [:: x] AT_none (Ox86 (MOV Uptr)) [::y].

Inductive mov_kind := 
  | MK_LEA 
  | MK_MOV.

Definition mov_ofs x mk y ofs := 
  if mk is MK_LEA then lea_ptr x y ofs 
  else
    if ofs == 0%Z then mov_ptr x y else lea_ptr x y ofs.

Definition is_nop is_spilling rmap (x:var) (sry:sub_region) : bool :=
  if is_spilling then
    if Mvar.get rmap.(var_region) x is Some srx then srx == sry
    else false
  else false.

Definition get_addr is_spilling rmap x dx sry mk y ofs := 
  let ir :=
    if is_nop is_spilling rmap x sry then nop
    else mov_ofs dx mk y ofs in
  let rmap := Region.set_move rmap x sry in
  (rmap, ir).

Definition get_ofs_sub aa ws e1 := 
  match mk_ofsi aa ws e1 with
  | None     => cerror "cannot take/set a subarray on a unknown starting position" 
  | Some ofs => ok ofs
  end.

Definition get_Lvar_sub lv := 
  match lv with
  | Lvar x => ok (x, None)
  | Lasub aa ws len x e1 =>
    Let ofs := get_ofs_sub aa ws e1 in
    ok (x, Some (ofs, arr_size ws len))
  | _      => cerror "variable/subarray excepted : 1"
  end.

Definition get_Pvar_sub e := 
  match e with
  | Pvar x => ok (x, None)
  | Psub aa ws len x e1 =>
    Let ofs := get_ofs_sub aa ws e1 in
    ok (x, Some (ofs, arr_size ws len))
  | _      => cerror "variable/subarray excepted : 2" 
  end.

(* TODO : currently, we check that the source array is valid and set the target
   array as valid too. We could, instead, give the same validity to the target
   array as the source one.
   [check_vpk] should be replaced with some function returning the valid bytes
   of y...
*)
(* Precondition is_sarr ty *)
Definition alloc_array_move rmap r e :=
  Let xsub := get_Lvar_sub r in
  Let ysub := get_Pvar_sub e in
  let '(x,subx) := xsub in
  let '(y,suby) := ysub in

  Let sryl := 
    let vy := y.(gv) in
    Let vk := get_var_kind y in
    let (ofs, len) := 
      match suby with
      | None => (0%Z, size_slot vy)
      | Some p => p
      end in
    match vk with
    | None => cerror "alloc_array_move"
    | Some vpk =>
      Let sry := check_vpk rmap vy vpk (Some ofs) len in
      match vpk with
      | VKglob (ofsy, ws) =>
        ok (sry, MK_LEA, Plvar (with_var vy pmap.(vrip)), (ofsy + ofs)%Z)
      | VKptr pk =>
        Let mklofs := 
          match pk with
          | Pdirect _ ofsy _ z sc =>
            ok (if sc is Slocal then MK_MOV else MK_LEA, Plvar (with_var vy (base_ptr sc)), (ofsy + z.(z_ofs) + ofs)%Z)
          | Pregptr p           => 
            ok (MK_MOV, Plvar (with_var vy p), ofs)
          | Pstkptr slot ofsy ws z x' => 
            Let _ := Region.check_stack_ptr rmap slot ws z x' in
            ok (MK_MOV, Pload Uptr (with_var vy pmap.(vrsp)) (cast_const ofsy), ofs)
          end in
        let '(mk, l, ofs) := mklofs in
        ok (sry, mk, l, ofs) 
      end
    end in
  let '(sry, mk, ey, ofs) := sryl in
  match subx with
  | None =>
    match get_local (v_var x) with
    | None    => cerror "register array remains" 
    | Some pk => 
      match pk with
      | Pdirect x' _ _ zx _ =>
        Let _  := assert ((x' == sry.(sr_region).(r_slot)) && (zx == sry.(sr_zone)))
                         (Cerr_stk_alloc "invalid source 1") in
        let rmap := Region.set_move rmap x sry in
        ok (rmap, nop)
      | Pregptr p =>
        ok (get_addr false rmap x (Lvar (with_var x p)) sry mk ey ofs)
      | Pstkptr slot ofsx ws z x' =>
        let: (rmap, ir) :=
          get_addr true rmap x (Lmem Uptr (with_var x pmap.(vrsp)) (cast_ptr ofsx)) sry mk ey ofs in
        Let rmap := Region.set_stack_ptr rmap slot ws z x' in
        ok (rmap, ir)
      end
    end
  | Some (ofs, len) =>
    match get_local (v_var x) with
    | None   => cerror "register array remains 2"
    | Some _ => 
      Let rmap := Region.set_arr_sub rmap x ofs len sry in
      ok (rmap, nop)
    end
  end.

Definition is_array_init e := 
  match e with
  | Parr_init _ => true
  | _ => false
  end.

Definition alloc_array_move_init rmap r e :=
  if is_array_init e then
    Let xsub := get_Lvar_sub r in
    let '(x,subx) := xsub in
    let (ofs, len) := 
      match subx with
      | None => (0%Z, size_slot (v_var x))
      | Some p => p
      end in
    Let sr := 
      match get_local (v_var x) with
      | None    => cerror "register array remains" 
      | Some pk => 
        match pk with
        | Pdirect x' _ ws z Slocal =>
          let z := {| z_ofs := z.(z_ofs) + ofs; z_len := len |} in
          ok (sub_region_stack x' ws z)
        | Pdirect _ _ _ _ Sglobal =>
          cerror "array init glob"
        | _ => 
          Let sr := get_sub_region rmap x in
          let z := {| z_ofs := sr.(sr_zone).(z_ofs) + ofs; z_len := len |} in
          ok {| sr_region := sr.(sr_region); sr_zone := z |}
        end
      end in
    let rmap := Region.set_arr_init rmap x sr in
    ok (rmap, nop)
  else alloc_array_move rmap r e.

Definition bad_lval_number := Cerr_stk_alloc "invalid number of lval".

Definition alloc_lvals rmap rs tys := 
  fmapM2 bad_lval_number alloc_lval rmap rs tys.

Section LOOP.

 Variable ii:instr_info.

 Variable check_c2 : region_map -> ciexec ((region_map * region_map) * (pexpr * (seq instr * seq instr)) ).

 Fixpoint loop2 (n:nat) (m:region_map) := 
    match n with
    | O => cierror ii (Cerr_Loop "stack_alloc")
    | S n =>
      Let m' := check_c2 m in
      if incl m m'.1.2 then ok (m'.1.1, m'.2)
      else loop2 n (merge m m'.1.2)
    end.

End LOOP.
 
Record stk_alloc_oracle_t :=
  { sao_align : wsize 
  ; sao_size: Z
  ; sao_extra_size: Z
  ; sao_max_size : Z
  ; sao_params : seq (option param_info)  (* Allocation of pointer params *)
  ; sao_return : seq (option nat)         (* Where to find the param input region *)
  ; sao_slots : seq (var * wsize * Z)  
  ; sao_alloc: seq (var * ptr_kind_init)   (* Allocation of local variables without params, and stk ptr *)
  ; sao_to_save: seq (var * Z)
  ; sao_rsp: saved_stack
  ; sao_return_address: return_address_location
  (* TODO : new field max_stack_size : maximal size of the stack needed to execute properly the program *)
  }.

Section PROG.

Context (local_alloc: funname -> stk_alloc_oracle_t).

Definition get_Pvar e := 
  match e with
  | Pvar x => ok x
  | _      => cerror "get_Pvar: variable excepted" 
  end.

Definition alloc_call_arg rmap (sao_param: option param_info) (e:pexpr) := 
  Let x := get_Pvar e in
  Let _ := assert (~~is_glob x) 
                  (Cerr_stk_alloc "global variable in argument of a call") in
  let xv := gv x in
  match sao_param, get_local xv with
  | None, None =>  
    ok (None, Pvar x)
  | None, Some _ => cerror "argument not a reg" 
  | Some pi, Some (Pregptr p) => 
    Let sr := Region.check_valid rmap xv (Some 0%Z) (size_slot xv) in
    Let _  := if pi.(pp_writable) then writable sr.(sr_region) else ok tt in
    Let _  := check_align sr pi.(pp_align) in
    ok (Some (pi.(pp_writable),sr), Pvar (mk_lvar (with_var xv p)))
  | Some _, _ => cerror "the argument should be a reg ptr" 
  end.

Definition disj_sub_regions sr1 sr2 :=
  ~~(region_same sr1.(sr_region) sr2.(sr_region)) || 
  disjoint_zones sr1.(sr_zone) sr2.(sr_zone).

Fixpoint check_all_disj (notwritables writables:seq sub_region) (srs:seq (option (bool * sub_region) * pexpr)) := 
  match srs with
  | [::] => true
  | (None, _) :: srs => check_all_disj notwritables writables srs
  | (Some (writable, sr), _) :: srs => 
    if all (disj_sub_regions sr) writables then 
      if writable then 
        if all (disj_sub_regions sr) notwritables then 
          check_all_disj notwritables (sr::writables) srs
        else false 
      else check_all_disj (sr::notwritables) writables srs
    else false 
  end.

Definition alloc_call_args rmap (sao_params: seq (option param_info)) (es:seq pexpr) := 
  Let es  := mapM2 (Cerr_stk_alloc "bad params info:please report") (alloc_call_arg rmap) sao_params es in
  Let _ := assert (check_all_disj [::] [::] es) 
           (Cerr_stk_alloc "some writable reg ptr are not disjoints") in
  ok es.

Definition check_lval_reg_call (r:lval) := 
  match r with
  | Lnone _ _ => ok tt
  | Lvar x =>
    match get_local x with 
    | None   => Let _ := check_diff x in ok tt
    | Some _ => cerror "call result should be stored in reg"
    end
  | Laset aa ws x e1 => cerror "array assignement in lval of a call"
  | Lasub aa ws len x e1 => cerror "sub array assignement in lval of a call"
  | Lmem ws x e1     => cerror "call result should be stored in reg"
  end.

Definition check_is_Lvar r (x:var) :=
  match r with
  | Lvar x' => x == x' 
  | _       => false 
  end.

Definition get_regptr (x:var_i) := 
  match get_local x with
  | Some (Pregptr p) => ok (with_var x p)
  | _ => cerror "variable should be a reg ptr" 
  end.

Definition get_Lvar lv := 
  match lv with
  | Lvar x => ok x
  | _      => cerror "get_Lvar variable excepted"
  end.

Definition alloc_lval_call (srs:seq (option (bool * sub_region) * pexpr)) rmap (r: lval) (i:option nat) :=
  match i with
  | None => 
    Let _ := check_lval_reg_call r in
    ok (rmap, r)
  | Some i => 
    match nth (None, Pconst 0) srs i with
    | (Some (_,mp), _) =>
      Let x := get_Lvar r in
      Let p := get_regptr x in
      Let rmap := Region.set_arr_call rmap (v_var x) mp in
      ok (rmap, Lvar p)
    | (None, _) => cerror "alloc_r_call : please report"
    end
  end.

Definition alloc_call_res rmap srs ret_pos rs := 
  fmapM2 bad_lval_number (alloc_lval_call srs) rmap rs ret_pos.

Definition alloc_call rmap ini rs fn es := 
  let sao := local_alloc fn in
  Let es  := alloc_call_args rmap sao.(sao_params) es in
  Let rs  := alloc_call_res  rmap es sao.(sao_return) rs in
  let es  := map snd es in
  ok (rs.1, Ccall ini rs.2 fn es).

Fixpoint alloc_i (rmap:region_map) (i: instr) : result instr_error (region_map * instr) :=
  let (ii, ir) := i in
  Let ir :=
    match ir with
    | Cassgn r t ty e => 
      if is_sarr ty then add_iinfo ii (alloc_array_move_init rmap r e) 
      else
        Let e := add_iinfo ii (alloc_e rmap e) in
        Let r := add_iinfo ii (alloc_lval rmap r ty) in
        ok (r.1, Cassgn r.2 t ty e)

    | Copn rs t o e => 
      Let e  := add_iinfo ii (alloc_es rmap e) in
      Let rs := add_iinfo ii (alloc_lvals rmap rs (sopn_tout o)) in
      ok (rs.1, Copn rs.2 t o e)               
  
    | Cif e c1 c2 => 
      Let e := add_iinfo ii (alloc_e rmap e) in
      Let c1 := fmapM alloc_i rmap c1 in
      Let c2 := fmapM alloc_i rmap c2 in
      let rmap:= merge c1.1 c2.1 in
      ok (rmap, Cif e c1.2 c2.2)
  
    | Cwhile a c1 e c2 => 
      let check_c rmap := 
        Let c1 := fmapM alloc_i rmap c1 in
        let rmap1 := c1.1 in
        Let e := add_iinfo ii (alloc_e rmap1 e) in
        Let c2 := fmapM alloc_i rmap1 c2 in
        ok ((rmap1, c2.1), (e, (c1.2, c2.2))) in
      Let r := loop2 ii check_c Loop.nb rmap in
      ok (r.1, Cwhile a r.2.2.1 r.2.1 r.2.2.2)

    | Ccall ini rs fn es =>
      add_iinfo ii (alloc_call rmap ini rs fn es) 

    | Cfor _ _ _  => cierror ii (Cerr_stk_alloc "don't deal with for loop")
    end in
  ok (ir.1, MkI ii ir.2).

End PROG.

End Section.

Definition init_stack_layout fn (ws_align: wsize) (l: seq (var * wsize * Z)) := 
  let add (xsr: var * wsize * Z) 
          (slp:  Mvar.t (Z * wsize) * Z) :=
    let '(stack, p) := slp in
    let '(x,ws,ofs) := xsr in
    if Mvar.get stack x is Some _ then cferror fn "duplicate stack region, please report"
    else
      if (p <= ofs)%CMP then
        let len := size_slot x in
        if (ws <= ws_align)%CMP then
          if (Z.land ofs (wsize_size ws - 1) == 0)%Z then
            let stack := Mvar.set stack x (ofs, ws) in
            ok (stack, (ofs + len)%Z)
          else cferror fn "bad stack region alignment"
        else cferror fn "bad stack alignment" 
      else cferror fn "stack region overlap" in
  foldM add (Mvar.empty _, 0%Z) l.

Definition init_local_map vrip vrsp fn globals sao := 
  Let sp := init_stack_layout fn sao.(sao_align) sao.(sao_slots) in
  let '(stack, size) := sp in
  if (size <= sao.(sao_size))%CMP then
    let add_alloc (xpk:var * ptr_kind_init) (lrx: Mvar.t ptr_kind * region_map * Sv.t) :=
      let '(locals, rmap, sv) := lrx in
      let '(x, pk) := xpk in
      if Sv.mem x sv then cferror fn "invalid reg pointer, please report"
      else
        Let svrmap := 
          match pk with
          | PIdirect x' z sc =>
            let vars := if sc is Slocal then stack else globals in
            match Mvar.get vars x' with
            | None => cferror fn "unknown region, please report"
            | Some (ofs', ws') =>
              if [&& (size_slot x <= z.(z_len))%CMP, (0%Z <= z.(z_ofs))%CMP &
                     ((z.(z_ofs) + z.(z_len))%Z <= size_slot x')%CMP] then
                let rmap :=
                  if sc is Slocal then
                    let sr := sub_region_stack x' ws' z in
                    Region.set_arr_init rmap x sr
                  else
                    rmap
                in
                ok (sv, Pdirect x' ofs' ws' z sc, rmap)
              else cferror fn "invalid slot, please report"
            end
          | PIstkptr x' z xp =>
            match Mvar.get stack x' with
            | None => cferror fn "unknown stack region, please report"
            | Some (ofs', ws') =>
              if Sv.mem xp sv then cferror fn "invalid stk ptr (not uniq), please report"
              else                
                if [&& (Uptr <= ws')%CMP,
                    (0%Z <= z.(z_ofs))%CMP & 
                    ((z.(z_ofs) + z.(z_len))%Z <= size_slot x')%CMP] then
                  ok (Sv.add xp sv, Pstkptr x' ofs' ws' z xp, rmap)
              else cferror fn "invalid ptr kind, please report"
            end
          | PIregptr p => 
            if Sv.mem p sv then cferror fn "invalid reg pointer already exists, please report"
            else if vtype p != sword Uptr then cferror fn "invalid pointer type, please report"
            else ok (Sv.add p sv, Pregptr p, rmap) 
          end in
        let '(sv,pk, rmap) := svrmap in
        let locals := Mvar.set locals x pk in
        ok (locals, rmap, sv) in
    let sv := Sv.add vrip (Sv.add vrsp Sv.empty) in
    Let aux := foldM add_alloc (Mvar.empty _, Region.empty, sv) sao.(sao_alloc) in
    let '(locals, rmap, sv) := aux in
    ok (stack, locals, rmap, sv)
  else cferror fn "stack size, please report".

(* TODO : move *)
Definition add_err_fun (A : Type) (f : funname) (r : cexec A) :=
  match r with
  | ok _ a => ok a
  | Error e => Error (Ferr_fun f e)
  end.

(** For each function, the oracle returns:
  - the size of the stack block;
  - an allocation for local variables;
  - an allocation for the variables to save;
  - where to save the stack pointer (of the caller); (* TODO: merge with above? *)
  - how to pass the return address (non-export functions only)

  It can call back the partial stack-alloc transformation that given an oracle (size of the stack block and allocation of stack variables)
  will transform the body of the current function.

  The oracle is implemented as follows:
   1/ stack allocation
   2/ Reg allocation
   3/ if we have remaining register to save the stack pointer we use on those register
      else
        4/ we restart stack allocation and we keep one position in the stack to save the stack pointer
        5/ Reg allocation
*)

Definition check_result pmap rmap params oi (x:var_i) := 
  match oi with
  | Some i =>
    match nth None params i with
    | Some r => 
      Let sr := check_valid rmap x (Some 0%Z) (size_slot x) in
      Let _  := assert (r == sr.(sr_region)) (Cerr_stk_alloc "invalid reg ptr in result") in
      Let p  := get_regptr pmap x in
      ok p
    | None => cerror "invalid function info:please report"
    end
  | None => 
    Let _ := check_var pmap x in
    ok x
  end.

Definition check_results pmap rmap params oi res := 
  mapM2 (Cerr_stk_alloc "invalid function info:please report")
        (check_result pmap rmap params) oi res.

Definition init_param accu pi (x:var_i) := 
  let: (disj, lmap, rmap) := accu in
  match pi with
  | None => ok (accu, (None, x))
  | Some pi => 
    Let _ := assert (vtype pi.(pp_ptr) == sword Uptr) (Cerr_stk_alloc "bad ptr type: please report") in
    Let _ := assert (~~Sv.mem pi.(pp_ptr) disj) (Cerr_stk_alloc "duplicate region: please report") in
    let r :=
      {| r_slot := pi.(pp_ptr);
         r_align := pi.(pp_align); r_writable := pi.(pp_writable) |} in
    ok (Sv.add pi.(pp_ptr) disj, 
        Mvar.set lmap x (Pregptr pi.(pp_ptr)),
        Region.set_full rmap x r,
        (Some r, with_var x pi.(pp_ptr)))
  end.

Definition init_params disj lmap rmap sao_params params :=
  fmapM2 (Cerr_stk_alloc "invalid function info:please report")
    init_param (disj, lmap, rmap) sao_params params.
   
Definition alloc_fd_aux p_extra mglob (local_alloc: funname -> stk_alloc_oracle_t) sao (f: _ufun_decl) : cfexec _ufundef :=
  let: (fn, fd) := f in
  let vrip := {| vtype := sword Uptr; vname := p_extra.(sp_rip) |} in
  let vrsp := var_of_register RSP in
  Let mstk := init_local_map vrip vrsp fn mglob sao in
  let '(stack, locals, rmap, disj) := mstk in
  (* adding params to the map *)
  Let rparams := 
    add_err_fun fn (init_params disj locals rmap sao.(sao_params) fd.(f_params)) in
  let: (sv, lmap, rmap, alloc_params) := rparams in
  let paramsi := map fst alloc_params in
  let params : seq var_i := map snd alloc_params in
  let pmap := {|
        vrip    := vrip;
        vrsp    := vrsp;
        globals := mglob;
        locals  := lmap;
        vnew    := sv;
      |} in
  Let rbody := add_finfo fn fn (fmapM (alloc_i pmap local_alloc) rmap fd.(f_body)) in
  let: (rmap, body) := rbody in
  Let res := 
      add_err_fun fn (check_results pmap rmap paramsi sao.(sao_return) fd.(f_res)) in
  ok {|
    f_iinfo := f_iinfo fd;
    f_tyin := map2 (fun o ty => if o is Some _ then sword Uptr else ty) sao.(sao_params) fd.(f_tyin); 
    f_params := params;
    f_body := body;
    f_tyout := map2 (fun o ty => if o is Some _ then sword Uptr else ty) sao.(sao_return) fd.(f_tyout);
    f_res := res;
    f_extra := f_extra fd |}.

Definition alloc_fd p_extra mglob (local_alloc: funname -> stk_alloc_oracle_t) (f: ufun_decl) :=
  let: sao := local_alloc f.1 in
  Let fd := alloc_fd_aux p_extra mglob local_alloc sao f in
  let f_extra := {|
        sf_align  := sao.(sao_align);
        sf_stk_sz := sao.(sao_size);
        sf_stk_max := sao.(sao_max_size);
        sf_stk_extra_sz := sao.(sao_extra_size);
        sf_to_save := sao.(sao_to_save);
        sf_save_stack := sao.(sao_rsp);
        sf_return_address := sao.(sao_return_address);
      |} in
  ok (f.1, swith_extra fd f_extra). 

Definition check_glob (m: Mvar.t (Z*wsize)) (data:seq u8) (gd:glob_decl) := 
  let x := gd.1 in
  match Mvar.get m x with
  | None => false 
  | Some (z, _) =>
    let n := Z.to_nat z in
    let data := drop n data in
    match gd.2 with
    | @Gword ws w =>
      let s := Z.to_nat (wsize_size ws) in 
      (s <= size data) && 
      (LE.decode ws (take s data) == w)
    | @Garr p t =>
      let s := Z.to_nat p in
      (s <= size data) &&
      all (fun i => 
             match WArray.get AAdirect U8 t (Z.of_nat i) with
             | Ok w => nth 0%R data i == w
             | _    => false
             end) (iota 0 s)
    end
  end.

Definition check_globs (gd:glob_decls) (m:Mvar.t (Z*wsize)) (data:seq u8) := 
  all (check_glob m data) gd.

Definition init_map (sz:Z) (l:list (var * wsize * Z)) : cexec (Mvar.t (Z*wsize)) :=
  let add (vp:var * wsize * Z) (mp:Mvar.t (Z*wsize) * Z) :=
    let '(v, ws, p) := vp in
    if (mp.2 <=? p)%Z then
      if is_align (wrepr _ p) ws then
        let s := size_slot v in
        cok (Mvar.set mp.1 v (p,ws), p + s)%Z
      else cerror "bad global alignment: please report"
    else cerror "global overlap: please report" in
  Let mp := foldM add (Mvar.empty (Z*wsize), 0%Z) l in
  if (mp.2 <=? sz)%Z then cok mp.1
  else cerror "global size:please report".

Definition alloc_prog rip global_data global_alloc local_alloc (P:_uprog) : cfexec _sprog :=
  Let mglob := add_err_msg (init_map (Z.of_nat (size global_data)) global_alloc) in
  let p_extra :=  {|
    sp_rip   := rip;
    sp_globs := global_data;
  |} in
  if rip == string_of_register RSP then Error (Ferr_msg (Cerr_stk_alloc "rip and rsp clash, please report"))
  else if check_globs P.(p_globs) mglob global_data then
    Let p_funs := mapM (alloc_fd p_extra mglob local_alloc) P.(p_funcs) in
    ok  {| p_funcs  := p_funs;
           p_globs := [::];
           p_extra := p_extra;
        |}
  else 
     Error (Ferr_msg (Cerr_stk_alloc "invalid data: please report")).
