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
Require Import strings word utils gen_map type var expr low_memory sem.
Require Import compiler_util byteset.
Require Import ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

Module Import E.

  Definition pass : string := "stack allocation".

  Definition stk_error_gen (internal:bool) (x:var_i) msg := {|
    pel_msg := msg;
    pel_fn := None;
    pel_fi := None;
    pel_ii := None;
    pel_vi := Some x.(v_info);
    pel_pass := Some pass;
    pel_internal := internal
  |}.

  Definition stk_error  := stk_error_gen false.
  Definition stk_ierror := stk_error_gen true.

  Definition stk_ierror_basic x msg :=
    stk_ierror x (pp_box [:: pp_s msg; pp_nobox [:: pp_s "("; pp_var x; pp_s ")"]]).

  Definition stk_error_no_var_gen (internal:bool) msg := {|
    pel_msg := pp_s msg;
    pel_fn := None;
    pel_fi := None;
    pel_ii := None;
    pel_vi := None;
    pel_pass := Some pass;
    pel_internal := internal
  |}.

  Definition stk_error_no_var  := stk_error_no_var_gen false.
  Definition stk_ierror_no_var := stk_error_no_var_gen true.

End E.

(* TODO: could [wsize_size] return a [positive] rather than a [Z]?
   If so, [size_of] could return a positive too.
*)
Definition size_of (t:stype) :=
  match t with
  | sword sz => wsize_size sz
  | sarr n   => Zpos n
  | sbool | sint => 1%Z
  end.

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

(* TODO: Z.land or is_align ?
   Could be just is_align (sub_region_addr sr) ws ? *)
Definition check_align x (sr:sub_region) ws :=
  Let _ := assert (ws <= sr.(sr_region).(r_align))%CMP
                  (stk_ierror_basic x "unaligned offset") in
  assert (Z.land sr.(sr_zone).(z_ofs) (wsize_size ws - 1) == 0)%Z
         (stk_ierror_basic x "unaligned sub offset").

Definition writable (x:var_i) (r:region) :=
  assert r.(r_writable)
    (stk_error x (pp_box [:: pp_s "cannot write to the constant pointer"; pp_var x])).

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

Definition get_sub_region (rmap:region_map) (x:var_i) :=
  match Mvar.get rmap.(var_region) x with
  | Some sr => ok sr
  | None => Error (stk_error x (pp_box [:: pp_s "no region associated to variable"; pp_var x]))
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

Definition check_valid (rmap:region_map) (x:var_i) ofs len :=
  (* we get the bytes associated to variable [x] *)
  Let sr := get_sub_region rmap x in
  let bytes := get_var_bytes rmap sr.(sr_region) x in
  let sr' := sub_region_at_ofs sr ofs len in
  let isub_ofs := interval_of_zone sr'.(sr_zone) in
  (* we check if [isub_ofs] is a subset of one of the intervals of [bytes] *)
  Let _   := assert (ByteSet.mem bytes isub_ofs)
                    (stk_error x (pp_box [:: pp_s "the region associated to variable"; pp_var x; pp_s "is partial"])) in
  ok (sr, sr').

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

(* TODO: take [bytes] as an argument ? *)
Definition set_pure_bytes rv (x:var) sr ofs len :=
  let z     := sr.(sr_zone) in
  let z1    := sub_zone_at_ofs z ofs len in
  let i     := interval_of_zone z1 in
  let bm    := get_bytes_map sr.(sr_region) rv in
  let bytes := if ofs is Some _ then ByteSet.add i (get_bytes x bm)
               else get_bytes x bm
  in
  (* clear all bytes corresponding to z1 *)
  let bm := clear_bytes_map i bm in
  (* set the bytes *)
  let bm := Mvar.set bm x bytes in
  Mr.set rv sr.(sr_region) bm.

Definition set_bytes rv (x:var_i) sr (ofs : option Z) (len : Z) :=
  Let _     := writable x sr.(sr_region) in
  ok (set_pure_bytes rv x sr ofs len).

(* TODO: as many functions are similar, maybe we could have one big function
   taking flags as arguments that tell whether we have to check align/check valid... *)
Definition set_sub_region rmap (x:var_i) sr (ofs : option Z) (len : Z) :=
  Let rv := set_bytes rmap x sr ofs len in
  ok {| var_region := Mvar.set rmap.(var_region) x sr;
        region_var := rv |}.

Definition sub_region_stkptr s ws z :=
  let r := {| r_slot := s; r_align := ws; r_writable := true |} in
  {| sr_region := r; sr_zone := z |}.

Definition set_stack_ptr (rmap:region_map) s ws z (x':var) :=
  let sr := sub_region_stkptr s ws z in
  let rv := set_pure_bytes rmap x' sr (Some 0)%Z (wsize_size Uptr) in
  {| var_region := rmap.(var_region);
     region_var := rv |}.

(* TODO: fusion with check_valid ? *)
Definition check_stack_ptr rmap s ws z x' :=
  let sr := sub_region_stkptr s ws z in
  let z := sub_zone_at_ofs z (Some 0)%Z (wsize_size Uptr) in
  let i := interval_of_zone z in
  let bytes := get_var_bytes rmap sr.(sr_region) x' in
  ByteSet.mem bytes i.

(* Precondition size_of x = ws && length sr.sr_zone = wsize_size ws *)
Definition set_word rmap (x:var_i) sr ws :=
  Let _ := check_align x sr ws in
  set_sub_region rmap x sr (Some 0)%Z (size_slot x).

(* If we write to array [x] at offset [ofs], we invalidate the corresponding
   memory zone for the other variables, and mark it as valid for [x].
   The offset [ofs] can be None, meaning its exact value is not known. In this
   case, the full zone [z] associated to array [x] is invalidated for the
   other variables, and remains the zone associated to [x]. It is a safe
   approximation.
*)
(* [set_word], [set_stack_ptr] and [set_arr_word] could be factorized? -> think more about it *)
Definition set_arr_word (rmap:region_map) (x:var_i) ofs ws :=
  Let sr := get_sub_region rmap x in
  Let _ := check_align x sr ws in
  set_sub_region rmap x sr ofs (wsize_size ws).

Definition set_arr_call rmap x sr := set_sub_region rmap x sr (Some 0)%Z (size_slot x).

Definition set_move_bytes rv x sr :=
  let bm := get_bytes_map sr.(sr_region) rv in
  let bytes := get_bytes x bm in
  let bm := Mvar.set bm x (ByteSet.add (interval_of_zone sr.(sr_zone)) bytes) in
  Mr.set rv sr.(sr_region) bm.

Definition set_move_sub (rmap:region_map) x sr :=
  let rv := set_move_bytes rmap x sr in
  {| var_region := rmap.(var_region);
     region_var := rv |}.

Definition set_arr_sub (rmap:region_map) (x:var_i) ofs len sr_from :=
  Let sr := get_sub_region rmap x in
  let sr' := sub_region_at_ofs sr (Some ofs) len in
  Let _ := assert (sr' == sr_from)
                  (stk_ierror x
                    (pp_box [::
                      pp_s "the assignment to sub-array"; pp_var x;
                      pp_s "cannot be turned into a nop: source and destination regions are not equal"]))
  in
  ok (set_move_sub rmap x sr').

(* identical to [set_sub_region], except clearing
   TODO: fusion with set_arr_sub ? not sure its worth
*)
Definition set_move (rmap:region_map) (x:var) sr :=
  let rv := set_move_bytes rmap x sr in
  {| var_region := Mvar.set rmap.(var_region) x sr;
     region_var := rv |}.

Definition set_arr_init rmap x sr := set_move rmap x sr.

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
       Mvar.map2 (fun _ osr1 osr2 =>
        match osr1, osr2 with
        | Some sr1, Some sr2 => if sr1 == sr2 then osr1 else None
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

Section CHECK.

(* The code in this file is called twice.
   - First, it is called from the stack alloc OCaml oracle. Indeed, the oracle
     returns initial results, and performs stack and reg allocation using
     these results. Based on the program that it obtains,
     it fixes some of the results and returns them.
   - Second, it is called as a normal compilation pass on the results returned
     by the oracle.

   When the code is called from the OCaml oracle, all the checks
   that are performed so that the pass can be proved correct are actually not
   needed. We introduce this boolen [check] to deactivate some of the tests
   when the code is called from the oracle.

   TODO: deactivate more tests (or even do not use rmap) when [check] is [false]
*)
Variable (check : bool).

Definition assert_check E b (e:E) :=
  if check then assert b e
  else ok tt.


Section Section.

Variables (pmap:pos_map).

Section ALLOC_E.

Variables (rmap: region_map).

Definition get_global (x:var_i) := 
  match Mvar.get pmap.(globals) x with
  | None => Error (stk_ierror_basic x "unallocated global variable")
  | Some z => ok z
  end.

Definition get_local (x:var) := Mvar.get pmap.(locals) x.

Definition check_diff (x:var_i) :=
  if Sv.mem x pmap.(vnew) then
    Error (stk_ierror_basic x "the code writes to one of the new variables")
  else ok tt.

Definition check_var (x:var_i) := 
  match get_local x with
  | None => ok tt
  | Some _ =>
    Error (stk_error x (pp_box [::
      pp_var x; pp_s "is a stack variable, but a reg variable is expected"]))
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

Definition addr_from_pk (x:var_i) (pk:ptr_kind) :=
  match pk with
  | Pdirect _ ofs _ z sc => ok (with_var x (base_ptr sc), ofs + z.(z_ofs))
  | Pregptr p            => ok (with_var x p,             0)
  | Pstkptr _ _ _ _ _    =>
    Error (stk_error x (pp_box [::
      pp_var x; pp_s "is a stack pointer, it should not appear in an expression"]))
  end%Z.

Definition addr_from_vpk x (vpk:vptr_kind) :=
  match vpk with
  | VKglob zws => ok (with_var x pmap.(vrip), zws.1)
  | VKptr pk => addr_from_pk x pk
  end.

Definition mk_addr_ptr x aa ws (pk:ptr_kind) (e1:pexpr) :=
  Let xofs := addr_from_pk x pk in
  ok (xofs.1, mk_ofs aa ws e1 xofs.2).

Definition mk_addr x aa ws (vpk:vptr_kind) (e1:pexpr) :=
  Let xofs := addr_from_vpk x vpk in
  ok (xofs.1, mk_ofs aa ws e1 xofs.2).

Definition get_var_kind x :=
  let xv := x.(gv) in
  if is_glob x then
    Let z := get_global xv in
    ok (Some (VKglob z))
  else 
    ok (omap VKptr (get_local xv)).

Definition sub_region_full x r :=
  let z := {| z_ofs := 0; z_len := size_slot x |} in
  {| sr_region := r; sr_zone := z |}.

Definition sub_region_glob x ws :=
  let r := {| r_slot := x; r_align := ws; r_writable := false |} in
  sub_region_full x r.

Definition check_vpk rmap (x:var_i) vpk ofs len :=
  match vpk with
  | VKglob (_, ws) =>
    let sr := sub_region_glob x ws in
    ok (sr, sub_region_at_ofs sr ofs len)
  | VKptr _pk => 
    check_valid rmap x ofs len
  end.

(* We could write [check_vpk] as follows.
  Definition check_vpk' rmap (x : gvar) ofs len :=
    let (sr, bytes) := check_gvalid rmap x in
    let sr' := sub_region_at_ofs sr.(sr_zone) ofs len in
    let isub_ofs := interval_of_zone sr'.(sr_zone) in
    (* we check if [isub_ofs] is a subset of one of the intervals of [bytes] *)
    (* useless test when [x] is glob, but factorizes call to [sub_region_at_ofs] *)
    Let _   := assert (ByteSet.mem bytes isub_ofs)
                      (Cerr_stk_alloc "check_valid: the region is partial") in
    ok sr'.
*)

Definition check_vpk_word rmap x vpk ofs ws :=
  Let srs := check_vpk rmap x vpk ofs (wsize_size ws) in
  check_align x srs.1 ws.

Fixpoint alloc_e (e:pexpr) := 
  match e with
  | Pconst _ | Pbool _ | Parr_init _ => ok e
  | Pvar   x =>
    let xv := x.(gv) in
    Let vk := get_var_kind x in
    match vk with
    | None => Let _ := check_diff xv in ok e
    | Some vpk => 
      if is_word_type (vtype xv) is Some ws then
        Let _ := check_vpk_word rmap xv vpk (Some 0%Z) ws in
        Let pofs := mk_addr xv AAdirect ws vpk (Pconst 0) in
        ok (Pload ws pofs.1 pofs.2)
      else Error (stk_ierror_basic xv "not a word variable in expression")
    end

  | Pget aa ws x e1 =>
    let xv := x.(gv) in
    Let e1 := alloc_e e1 in
    Let vk := get_var_kind x in
    match vk with
    | None => Let _ := check_diff xv in ok (Pget aa ws x e1)
    | Some vpk =>
      let ofs := mk_ofsi aa ws e1 in
      Let _ := check_vpk_word rmap xv vpk ofs ws in
      Let pofs := mk_addr xv aa ws vpk e1 in
      ok (Pload ws pofs.1 pofs.2)
    end

  | Psub aa ws len x e1 =>
    Error (stk_ierror_basic x.(gv) "Psub")

  | Pload ws x e1 =>
    Let _ := check_var x in
    Let _ := check_diff x in
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

Definition sub_region_pk x pk :=
  match pk with
  | Pdirect x ofs align sub Slocal => ok (sub_region_stack x align sub)
  | _ => Error (stk_ierror x (pp_box [:: pp_var x; pp_s "is not in the stack"]))
  end.

Definition alloc_lval (rmap: region_map) (r:lval) (ty:stype) :=
  match r with
  | Lnone _ _ => ok (rmap, r)

  | Lvar x =>
    (* TODO: could we remove this [check_diff] and use an invariant in the proof instead? *)
    match get_local x with
    | None => Let _ := check_diff x in ok (rmap, r)
    | Some pk => 
      if is_word_type (vtype x) is Some ws then 
        if subtype (sword ws) ty then 
          Let pofs := mk_addr_ptr x AAdirect ws pk (Pconst 0) in
          Let sr   := sub_region_pk x pk in
          let r := Lmem ws pofs.1 pofs.2 in
          Let rmap := Region.set_word rmap x sr ws in
          ok (rmap, r)
        else Error (stk_ierror_basic x "invalid type for assignment")
      else Error (stk_ierror_basic x "not a word variable in assignment")
    end

  | Laset aa ws x e1 =>
    (* TODO: could we remove this [check_diff] and use an invariant in the proof instead? *)
    Let e1 := alloc_e rmap e1 in
    match get_local x with
    | None => Let _ := check_diff x in ok (rmap, Laset aa ws x e1)
    | Some pk => 
      let ofs := mk_ofsi aa ws e1 in 
      Let rmap := set_arr_word rmap x ofs ws in
      Let pofs := mk_addr_ptr x aa ws pk e1 in
      let r := Lmem ws pofs.1 pofs.2 in
      ok (rmap, r)
    end

  | Lasub aa ws len x e1 =>
    Error (stk_ierror_basic x "Lasub")

  | Lmem ws x e1 =>
    Let _ := check_var x in
    Let _ := check_diff x in
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

(* [is_spilling] is used for stack pointers. *)
Definition is_nop is_spilling rmap (x:var) (sry:sub_region) : bool :=
  if is_spilling is Some (s, ws, z, f) then
    if Mvar.get rmap.(var_region) x is Some srx then
      (srx == sry) && check_stack_ptr rmap s ws z f
    else false
  else false.

(* TODO: better error message *)
Definition get_addr is_spilling rmap x dx sry mk y ofs := 
  let ir :=
    if is_nop is_spilling rmap x sry then nop
    else
      mov_ofs dx mk y ofs in
  let rmap := Region.set_move rmap x sry in
  (rmap, ir).

Definition get_ofs_sub aa ws x e1 := 
  match mk_ofsi aa ws e1 with
  | None     => Error (stk_ierror_basic x "cannot take/set a subarray on a unknown starting position")
  | Some ofs => ok ofs
  end.

Definition get_Lvar_sub lv := 
  match lv with
  | Lvar x => ok (x, None)
  | Lasub aa ws len x e1 =>
    Let ofs := get_ofs_sub aa ws x e1 in
    ok (x, Some (ofs, arr_size ws len))
  | _      => Error (stk_ierror_no_var "get_Lvar_sub: variable/subarray expected")
  end.

Definition get_Pvar_sub e := 
  match e with
  | Pvar x => ok (x, None)
  | Psub aa ws len x e1 =>
    Let ofs := get_ofs_sub aa ws x.(gv) e1 in
    ok (x, Some (ofs, arr_size ws len))
  | _      => Error (stk_ierror_no_var "get_Pvar_sub: variable/subarray expected")
  end.

Definition is_stack_ptr vpk :=
  match vpk with
  | VKptr (Pstkptr s ofs ws z f) => Some (s, ofs, ws, z, f)
  | _ => None
  end.

(* Not so elegant: function [addr_from_vpk] can fail, but it
   actually fails only on the [Pstkptr] case, that is treated apart.
   Thus function [mk_addr_pexpr] never fails, but this is not checked statically.
*)
Definition mk_addr_pexpr rmap x vpk :=
  if is_stack_ptr vpk is Some (s, ofs, ws, z, f) then
    Let _   := assert (check_stack_ptr rmap s ws z f)
                      (stk_error x (pp_box [:: pp_s "the stack pointer"; pp_var x; pp_s "is no longer valid"])) in
    ok (Pload Uptr (with_var x pmap.(vrsp)) (cast_const (ofs + z.(z_ofs))), 0%Z)
  else
    Let xofs := addr_from_vpk x vpk in
    ok (Plvar xofs.1, xofs.2).

Definition mk_mov vpk :=
  match vpk with
  | VKglob _ | VKptr (Pdirect _ _ _ _ Slocal) => MK_LEA
  | _ => MK_MOV
  end.

(* TODO: the check [is_lvar] was removed, was it really on purpose? *)
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
      end
    in
    match vk with
    | None => Error (stk_ierror_basic vy "register array remains")
    | Some vpk =>
      Let srs := check_vpk rmap vy vpk (Some ofs) len in
      let sry := srs.2 in
      Let eofs := mk_addr_pexpr rmap vy vpk in
      let mk := mk_mov vpk in
      ok (sry, mk, eofs.1, (eofs.2 + ofs)%Z)
    end
  in
  let '(sry, mk, ey, ofs) := sryl in
  match subx with
  | None =>
    match get_local (v_var x) with
    | None    => Error (stk_ierror_basic x "register array remains")
    | Some pk => 
      match pk with
      | Pdirect s _ ws zx sc =>
        let sr := sub_region_direct s ws sc zx in
        Let _  :=
          assert (sr == sry)
                 (stk_ierror x
                    (pp_box [::
                      pp_s "the assignment to array"; pp_var x;
                      pp_s "cannot be turned into a nop: source and destination regions are not equal"]))
        in
        let rmap := Region.set_move rmap x sry in
        ok (rmap, nop)
      | Pregptr p =>
        ok (get_addr None rmap x (Lvar (with_var x p)) sry mk ey ofs)
      | Pstkptr slot ofsx ws z x' =>
        let (rmap, ir) :=
          get_addr (Some (slot, ws, z, x')) rmap x (Lmem Uptr (with_var x pmap.(vrsp)) (cast_const (ofsx + z.(z_ofs)))) sry mk ey ofs in
        ok (Region.set_stack_ptr rmap slot ws z x', ir)
      end
    end
  | Some (ofs, len) =>
    match get_local (v_var x) with
    | None   => Error (stk_ierror_basic x "register array remains")
    | Some _ => 
      Let rmap := Region.set_arr_sub rmap x ofs len sry in
      ok (rmap, nop)
    end
  end.

(* This function is also defined in array_init.v *)
(* TODO: clean *)
Definition is_array_init e := 
  match e with
  | Parr_init _ => true
  | _ => false
  end.

(* We do not update the [var_region] part *)
(* there seems to be an invariant: all Pdirect are in the rmap *)
(* long-term TODO: we can avoid putting PDirect in the rmap (look in pmap instead) *)
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
      | None    => Error (stk_ierror_basic x "register array remains")
      | Some pk =>
        match pk with
        | Pdirect x' _ ws z sc =>
          if sc is Slocal then
            ok (sub_region_stack x' ws z)
          else
            Error (stk_error x (pp_box [:: pp_s "cannot initialize glob array"; pp_var x]))
        | _ => 
          get_sub_region rmap x
        end
      end in
    let sr := sub_region_at_ofs sr (Some ofs) len in
    let rmap := Region.set_move_sub rmap x sr in
    ok (rmap, nop)
  else alloc_array_move rmap r e.

Definition bad_lval_number := stk_ierror_no_var "invalid number of lval".

Definition alloc_lvals rmap rs tys := 
  fmapM2 bad_lval_number alloc_lval rmap rs tys.

Section LOOP.

 Variable ii:instr_info.

 Variable check_c2 : region_map -> cexec ((region_map * region_map) * (pexpr * (seq instr * seq instr)) ).

 Fixpoint loop2 (n:nat) (m:region_map) := 
    match n with
    | O => Error (pp_at_ii ii (stk_ierror_no_var "loop2"))
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
  }.

Section PROG.

Context (local_alloc: funname -> stk_alloc_oracle_t).

Definition get_Pvar e := 
  match e with
  | Pvar x => ok x
  | _      => Error (stk_ierror_no_var "get_Pvar: variable expected")
  end.

(* The name is chosen to be similar to [set_pure_bytes] and [set_move_bytes],
   but there are probably better ideas.
   TODO: factorize [set_clear_bytes] and [set_pure_bytes] ?
*)
Definition set_clear_bytes rv sr ofs len :=
  let z     := sr.(sr_zone) in
  let z1    := sub_zone_at_ofs z ofs len in
  let i     := interval_of_zone z1 in
  let bm    := get_bytes_map sr.(sr_region) rv in
  (* clear all bytes corresponding to z1 *)
  let bm := clear_bytes_map i bm in
  Mr.set rv sr.(sr_region) bm.

Definition set_clear_pure rmap sr ofs len :=
  {| var_region := rmap.(var_region);
     region_var := set_clear_bytes rmap sr ofs len |}.

Definition set_clear rmap x sr ofs len :=
  Let _ := writable x sr.(sr_region) in
  ok (set_clear_pure rmap sr ofs len).

(* We clear the arguments. This is not necessary in the classic case, because
   we also clear them when assigning the results in alloc_call_res
   (this works if each writable reg ptr is returned (which is currently
   checked by the pretyper) and if each result variable has the same size
   as the corresponding input variable).
   But this complexifies the proof and needs a few more
   checks in stack_alloc to be valid. Thus, for the sake of simplicity, it was
   decided to make the clearing of the arguments twice : here and in
   alloc_call_res.

   We use two rmaps:
   - the initial rmap [rmap0] is used to check the validity of the sub-regions;
   - the current rmap [rmap] is [rmap0] with all the previous writable sub-regions cleared.
   Actually, we could use [rmap] to check the validity, and that would partially
   enforce that the arguments correspond to disjoint regions (in particular,
   writable sub-regions are pairwise disjoint), so with this version we could
   simplify check_all_disj. If we first check the validity and clear the writable regions,
   and then check the validity of the non-writable ones, we can even remove [check_all_disj].
   But the error message (disjoint regions) is much clearer when we have [check_all_disj],
   so I leave it as it is now.
*)
Definition alloc_call_arg_aux rmap0 rmap (sao_param: option param_info) (e:pexpr) := 
  Let x := get_Pvar e in
  Let _ := assert (~~is_glob x)
                  (stk_ierror_basic x.(gv) "global variable in argument of a call") in
  let xv := gv x in
  match sao_param, get_local xv with
  | None, None =>
    Let _ := check_diff xv in
    ok (rmap, (None, Pvar x))
  | None, Some _ => Error (stk_ierror_basic xv "argument not a reg")
  | Some pi, Some (Pregptr p) => 
    Let srs := Region.check_valid rmap0 xv (Some 0%Z) (size_slot xv) in
    let sr := srs.1 in
    Let rmap := if pi.(pp_writable) then set_clear rmap xv sr (Some 0%Z) (size_slot xv) else ok rmap in
    Let _  := check_align xv sr pi.(pp_align) in
    ok (rmap, (Some (pi.(pp_writable),sr), Pvar (mk_lvar (with_var xv p))))
  | Some _, _ => Error (stk_ierror_basic xv "the argument should be a reg ptr")
  end.

Definition alloc_call_args_aux rmap sao_params es :=
  fmapM2 (stk_ierror_no_var "bad params info") (alloc_call_arg_aux rmap) rmap sao_params es.

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
  Let es := alloc_call_args_aux rmap sao_params es in
  Let _  := assert (check_all_disj [::] [::] es.2)
                   (stk_error_no_var "some writable reg ptr are not disjoints") in
  ok es.

Definition check_lval_reg_call (r:lval) := 
  match r with
  | Lnone _ _ => ok tt
  | Lvar x =>
    match get_local x with
    | None   => Let _ := check_diff x in ok tt
    | Some _ => Error (stk_ierror_basic x "call result should be stored in reg")
    end
  | Laset aa ws x e1 => Error (stk_ierror_basic x "array assignement in lval of a call")
  | Lasub aa ws len x e1 => Error (stk_ierror_basic x "sub-array assignement in lval of a call")
  | Lmem ws x e1     => Error (stk_ierror_basic x "call result should be stored in reg")
  end.

Definition check_is_Lvar r (x:var) :=
  match r with
  | Lvar x' => x == x' 
  | _       => false 
  end.

Definition get_regptr (x:var_i) := 
  match get_local x with
  | Some (Pregptr p) => ok (with_var x p)
  | _ => Error (stk_ierror x (pp_box [:: pp_s "variable"; pp_var x; pp_s "should be a reg ptr"]))
  end.

Definition alloc_lval_call (srs:seq (option (bool * sub_region) * pexpr)) rmap (r: lval) (i:option nat) :=
  match i with
  | None => 
    Let _ := check_lval_reg_call r in
    ok (rmap, r)
  | Some i => 
    match nth (None, Pconst 0) srs i with
    | (Some (_,sr), _) =>
      match r with
      | Lnone i _ => ok (rmap, Lnone i (sword Uptr))
      | Lvar x =>
        Let p := get_regptr x in
        Let rmap := Region.set_arr_call rmap x sr in
        (* TODO: Lvar p or Lvar (with_var x p) like in alloc_call_arg? *)
        ok (rmap, Lvar p)
      | Laset aa ws x e1 => Error (stk_ierror_basic x "array assignement in lval of a call")
      | Lasub aa ws len x e1 => Error (stk_ierror_basic x "sub-array assignement in lval of a call")
      | Lmem ws x e1     => Error (stk_ierror_basic x "call result should be stored in reg ptr")
      end
    | (None, _) => Error (stk_ierror_no_var "alloc_lval_call")
    end
  end.

Definition alloc_call_res rmap srs ret_pos rs := 
  fmapM2 bad_lval_number (alloc_lval_call srs) rmap rs ret_pos.

Definition is_RAnone ral :=
  if ral is RAnone then true else false.

Definition alloc_call (sao_caller:stk_alloc_oracle_t) rmap ini rs fn es := 
  let sao_callee := local_alloc fn in
  Let es  := alloc_call_args rmap sao_callee.(sao_params) es in
  let '(rmap, es) := es in
  Let rs  := alloc_call_res rmap es sao_callee.(sao_return) rs in (*
  Let _   := assert_check (~~ is_RAnone sao_callee.(sao_return_address))
               (Cerr_stk_alloc "cannot call export function")
  in *)
  Let _   :=
    let local_size :=
      if is_RAnone sao_caller.(sao_return_address) then
        (sao_caller.(sao_size) + sao_caller.(sao_extra_size) + wsize_size sao_caller.(sao_align) - 1)%Z
      else
        (round_ws sao_caller.(sao_align) (sao_caller.(sao_size) + sao_caller.(sao_extra_size)))%Z
    in
    assert_check (local_size + sao_callee.(sao_max_size) <=? sao_caller.(sao_max_size))%Z
                 (stk_ierror_no_var "error in max size computation")
  in
  Let _   := assert_check (sao_callee.(sao_align) <= sao_caller.(sao_align))%CMP
                          (stk_ierror_no_var "non aligned function call")
  in
  let es  := map snd es in
  ok (rs.1, Ccall ini rs.2 fn es).

Fixpoint alloc_i sao (rmap:region_map) (i: instr) : cexec (region_map * instr) :=
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
      Let c1 := fmapM (alloc_i sao) rmap c1 in
      Let c2 := fmapM (alloc_i sao) rmap c2 in
      let rmap:= merge c1.1 c2.1 in
      ok (rmap, Cif e c1.2 c2.2)

    | Cwhile a c1 e c2 => 
      let check_c rmap := 
        Let c1 := fmapM (alloc_i sao) rmap c1 in
        let rmap1 := c1.1 in
        Let e := add_iinfo ii (alloc_e rmap1 e) in
        Let c2 := fmapM (alloc_i sao) rmap1 c2 in
        ok ((rmap1, c2.1), (e, (c1.2, c2.2))) in
      Let r := loop2 ii check_c Loop.nb rmap in
      ok (r.1, Cwhile a r.2.2.1 r.2.1 r.2.2.2)

    | Ccall ini rs fn es =>
      add_iinfo ii (alloc_call sao rmap ini rs fn es) 

    | Cfor _ _ _  => Error (pp_at_ii ii (stk_ierror_no_var "don't deal with for loop"))
    end in
  ok (ir.1, MkI ii ir.2).

End PROG.

End Section.

Definition init_stack_layout (mglob : Mvar.t (Z * wsize)) sao := 
  let add (xsr: var * wsize * Z) 
          (slp:  Mvar.t (Z * wsize) * Z) :=
    let '(stack, p) := slp in
    let '(x,ws,ofs) := xsr in
    if Mvar.get stack x is Some _ then Error (stk_ierror_no_var "duplicate stack region")
    else if Mvar.get mglob x is Some _ then Error (stk_ierror_no_var "a region is both glob and stack")
    else
      if (p <= ofs)%CMP then
        let len := size_slot x in
        if (ws <= sao.(sao_align))%CMP then
          if (Z.land ofs (wsize_size ws - 1) == 0)%Z then
            let stack := Mvar.set stack x (ofs, ws) in
            ok (stack, (ofs + len)%Z)
          else Error (stk_ierror_no_var "bad stack region alignment")
        else Error (stk_ierror_no_var "bad stack alignment")
      else Error (stk_ierror_no_var "stack region overlap") in
  Let sp := foldM add (Mvar.empty _, 0%Z) sao.(sao_slots) in
  let '(stack, size) := sp in
  if (size <= sao.(sao_size))%CMP then ok stack
  else Error (stk_ierror_no_var "stack size").

Definition add_alloc globals stack (xpk:var * ptr_kind_init) (lrx: Mvar.t ptr_kind * region_map * Sv.t) :=
  let '(locals, rmap, sv) := lrx in
  let '(x, pk) := xpk in
  if Sv.mem x sv then Error (stk_ierror_no_var "invalid reg pointer")
  else if Mvar.get locals x is Some _ then
    Error (stk_ierror_no_var "the oracle returned two results for the same var")
  else
    Let svrmap := 
      match pk with
      | PIdirect x' z sc =>
        let vars := if sc is Slocal then stack else globals in
        match Mvar.get vars x' with
        | None => Error (stk_ierror_no_var "unknown region")
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
          else Error (stk_ierror_no_var "invalid slot")
        end
      | PIstkptr x' z xp =>
        if ~~ is_sarr x.(vtype) then
          Error (stk_ierror_no_var "a stk ptr variable must be an array")
        else
        match Mvar.get stack x' with
        | None => Error (stk_ierror_no_var "unknown stack region")
        | Some (ofs', ws') =>
          if Sv.mem xp sv then Error (stk_ierror_no_var "invalid stk ptr (not unique)")
          else if xp == x then Error (stk_ierror_no_var "a pseudo-var is equal to a program var")
          else if Mvar.get locals xp is Some _ then Error (stk_ierror_no_var "a pseudo-var is equal to a program var")
          else
            if [&& (Uptr <= ws')%CMP,
                (0%Z <= z.(z_ofs))%CMP,
                (Z.land z.(z_ofs) (wsize_size U64 - 1) == 0)%Z,
                (wsize_size Uptr <= z.(z_len))%CMP &
                ((z.(z_ofs) + z.(z_len))%Z <= size_slot x')%CMP] then
              ok (Sv.add xp sv, Pstkptr x' ofs' ws' z xp, rmap)
          else Error (stk_ierror_no_var "invalid ptr kind")
        end
      | PIregptr p => 
        if ~~ is_sarr x.(vtype) then
          Error (stk_ierror_no_var "a reg ptr variable must be an array")
        else
        if Sv.mem p sv then Error (stk_ierror_no_var "invalid reg pointer already exists")
        else if Mvar.get locals p is Some _ then Error (stk_ierror_no_var "a pointer is equal to a program var")
        else if vtype p != sword Uptr then Error (stk_ierror_no_var "invalid pointer type")
        else ok (Sv.add p sv, Pregptr p, rmap) 
      end in
    let '(sv,pk, rmap) := svrmap in
    let locals := Mvar.set locals x pk in
    ok (locals, rmap, sv).

Definition init_local_map vrip vrsp globals stack sao :=
  let sv := Sv.add vrip (Sv.add vrsp Sv.empty) in
  Let aux := foldM (add_alloc globals stack) (Mvar.empty _, Region.empty, sv) sao.(sao_alloc) in
  let '(locals, rmap, sv) := aux in
  ok (locals, rmap, sv).

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

Definition check_result pmap rmap paramsi params oi (x:var_i) :=
  match oi with
  | Some i =>
    match nth None paramsi i with
    | Some sr =>
      Let _ := assert (x.(vtype) == (nth x params i).(vtype))
                      (stk_ierror_no_var "reg ptr in result not corresponding to a parameter") in
      Let srs := check_valid rmap x (Some 0%Z) (size_slot x) in
      let sr' := srs.1 in
      Let _  := assert (sr == sr') (stk_ierror_no_var "invalid reg ptr in result") in
      Let p  := get_regptr pmap x in
      ok p
    | None => Error (stk_ierror_no_var "invalid function info")
    end
  | None => 
    Let _ := check_var pmap x in
    Let _ := check_diff pmap x in
    ok x
  end.

(* TODO: clean the 3 [all2] functions *)
Definition check_all_writable_regions_returned paramsi (ret_pos:seq (option nat)) :=
  all2 (fun i osr =>
    match osr with
    | Some sr => if sr.(sr_region).(r_writable) then Some i \in ret_pos else true
    | None => true
    end) (iota 0 (size paramsi)) paramsi.

Definition check_results pmap rmap paramsi params ret_pos res := 
  Let _ := assert (check_all_writable_regions_returned paramsi ret_pos)
                  (stk_ierror_no_var "a writable region is not returned")
  in
  mapM2 (stk_ierror_no_var "invalid function info")
        (check_result pmap rmap paramsi params) ret_pos res.

(* TODO: is duplicate region the best error msg ? *)
Definition init_param (mglob stack : Mvar.t (Z * wsize)) accu pi (x:var_i) := 
  let: (disj, lmap, rmap) := accu in
  Let _ := assert (~~ Sv.mem x disj) (stk_ierror_no_var "a parameter already exists") in
  if Mvar.get lmap x is Some _ then Error (stk_ierror_no_var "a stack variable also occurs as a parameter")
  else
  match pi with
  | None => ok (accu, (None, x))
  | Some pi => 
    Let _ := assert (vtype pi.(pp_ptr) == sword Uptr) (stk_ierror_no_var "bad ptr type") in
    Let _ := assert (~~Sv.mem pi.(pp_ptr) disj) (stk_ierror_no_var "duplicate region") in
    Let _ := assert (is_sarr x.(vtype)) (stk_ierror_no_var "bad reg ptr type") in
    if Mvar.get lmap pi.(pp_ptr) is Some _ then Error (stk_ierror_no_var "a pointer is equal to a local var")
    else if Mvar.get mglob x is Some _ then Error (stk_ierror_no_var "a region is both glob and param")
    else if Mvar.get stack x is Some _ then Error (stk_ierror_no_var "a region is both stack and param")
    else
    let r :=
      {| r_slot := x;
         r_align := pi.(pp_align); r_writable := pi.(pp_writable) |} in
    let sr := sub_region_full x r in
    ok (Sv.add pi.(pp_ptr) disj,
        Mvar.set lmap x (Pregptr pi.(pp_ptr)),
        set_move rmap x sr,
        (Some sr, with_var x pi.(pp_ptr)))
  end.

Definition init_params mglob stack disj lmap rmap sao_params params :=
  fmapM2 (stk_ierror_no_var "invalid function info")
    (init_param mglob stack) (disj, lmap, rmap) sao_params params.

Definition alloc_fd_aux p_extra mglob (local_alloc: funname -> stk_alloc_oracle_t) sao fd : cexec _ufundef :=
  let vrip := {| vtype := sword Uptr; vname := p_extra.(sp_rip) |} in
  let vrsp := {| vtype := sword Uptr; vname := p_extra.(sp_rsp) |} in
  Let stack := init_stack_layout mglob sao in
  Let mstk := init_local_map vrip vrsp mglob stack sao in
  let '(locals, rmap, disj) := mstk in
  (* adding params to the map *)
  Let rparams :=
    init_params mglob stack disj locals rmap sao.(sao_params) fd.(f_params) in
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
  Let _ := assert (0 <=? sao.(sao_extra_size))%Z
                  (stk_ierror_no_var "negative extra size")
  in
  Let _ :=
    let local_size :=
      if is_RAnone sao.(sao_return_address) then
        (sao.(sao_size) + sao.(sao_extra_size) + wsize_size sao.(sao_align) - 1)%Z
      else
        (round_ws sao.(sao_align) (sao.(sao_size) + sao.(sao_extra_size)))%Z
    in
    assert_check (local_size <=? sao.(sao_max_size))%Z
                 (stk_ierror_no_var "sao_max_size too small")
  in
  Let rbody := fmapM (alloc_i pmap local_alloc sao) rmap fd.(f_body) in
  let: (rmap, body) := rbody in
  Let res :=
      check_results pmap rmap paramsi fd.(f_params) sao.(sao_return) fd.(f_res) in
  ok {|
    f_info := f_info fd;
    f_tyin := map2 (fun o ty => if o is Some _ then sword Uptr else ty) sao.(sao_params) fd.(f_tyin); 
    f_params := params;
    f_body := body;
    f_tyout := map2 (fun o ty => if o is Some _ then sword Uptr else ty) sao.(sao_return) fd.(f_tyout);
    f_res := res;
    f_extra := f_extra fd |}.

Definition alloc_fd p_extra mglob (local_alloc: funname -> stk_alloc_oracle_t) fn fd :=
  let: sao := local_alloc fn in
  Let fd := alloc_fd_aux p_extra mglob local_alloc sao fd in
  let f_extra := {|
        sf_align  := sao.(sao_align);
        sf_stk_sz := sao.(sao_size);
        sf_stk_max := sao.(sao_max_size);
        sf_stk_extra_sz := sao.(sao_extra_size);
        sf_to_save := sao.(sao_to_save);
        sf_save_stack := sao.(sao_rsp);
        sf_return_address := sao.(sao_return_address);
      |} in
  ok (swith_extra fd f_extra).

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
             match read t (Z.of_nat i) U8 with
             | Ok w => nth 0%R data i == w
             | _    => false
             end) (iota 0 s)
    end
  end.

Definition check_globs (gd:glob_decls) (m:Mvar.t (Z*wsize)) (data:seq u8) := 
  all (check_glob m data) gd.

Definition init_map (sz:Z) (l:list (var * wsize * Z)) : cexec (Mvar.t (Z*wsize)) :=
  let add (vp:var * wsize * Z) (globals:Mvar.t (Z*wsize) * Z) :=
    let '(v, ws, p) := vp in
    if (globals.2 <=? p)%Z then
      if Z.land p (wsize_size ws - 1) == 0%Z then
        let s := size_slot v in
        ok (Mvar.set globals.1 v (p,ws), p + s)%Z
      else Error (stk_ierror_no_var "bad global alignment")
    else Error (stk_ierror_no_var "global overlap") in
  Let globals := foldM add (Mvar.empty (Z*wsize), 0%Z) l in
  if (globals.2 <=? sz)%Z then ok globals.1
  else Error (stk_ierror_no_var "global size").

Definition alloc_prog rip rsp global_data global_alloc local_alloc (P:_uprog) : cexec _sprog :=
  Let mglob := init_map (Z.of_nat (size global_data)) global_alloc in
  let p_extra :=  {|
    sp_rip   := rip;
    sp_rsp   := rsp;
    sp_globs := global_data;
  |} in
  if rip == rsp then Error (stk_ierror_no_var "rip and rsp clash")
  else if check_globs P.(p_globs) mglob global_data then
    Let p_funs := map_cfprog_name (alloc_fd p_extra mglob local_alloc) P.(p_funcs) in
    ok  {| p_funcs  := p_funs;
           p_globs := [::];
           p_extra := p_extra;
        |}
  else 
     Error (stk_ierror_no_var "invalid data").

End CHECK.
